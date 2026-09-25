import Leanline.Editor
import Leanline.Render
import Leanline.Reader
import Leanline.Prefs

/-!
# The `InputT` monad transformer

`InputT m` adds line-editing input to any monad `m` that can run `IO`. It is
run with `runInputT` (or one of its variants), which chooses between the
interactive terminal backend and plain line reading (when input is not a
terminal), loads and saves the history file, and restores the terminal on
exit, even when an exception escapes.

Input functions return typed results: `getInputLine` gives `none` at end of
input, and `getInputLineResult` additionally reports Ctrl-C as
`LineResult.interrupted` instead of raising anything.
-/

namespace Leanline

/-! ## Configuration -/

/-- Where input comes from. -/
inductive Behavior where
  /-- The terminal if standard input and output are terminals, otherwise
  unedited lines from standard input. -/
  | defaultBehavior
  /-- Unedited lines from a stream. -/
  | useStream (s : IO.FS.Stream)
  /-- Unedited lines from a file. -/
  | useFile (path : System.FilePath)
  /-- The controlling terminal (`/dev/tty`) even when standard input is
  redirected; falls back to `defaultBehavior` if there is none. -/
  | preferTerm

def defaultBehavior : Behavior := .defaultBehavior
def useFileHandle (h : IO.FS.Handle) : Behavior := .useStream (IO.FS.Stream.ofHandle h)
def useFile (path : System.FilePath) : Behavior := .useFile path
def preferTerm : Behavior := .preferTerm

/-- Program-level settings (preferences that belong to the user live in `Prefs`). -/
structure Settings (m : Type → Type) [Monad m] where
  complete : CompletionFunc m := noCompletion
  /-- History is loaded from and saved to this file. -/
  historyFile : Option System.FilePath := none
  /-- Add each non-blank line returned by `getInputLine` to the history. -/
  autoAddHistory : Bool := true
  /-- Extra key bindings, consulted before the built-in keymaps. -/
  keyBindings : Keymap := []
  /-- Multi-line input: when this returns `false` for the text entered so far,
  Enter inserts a line break instead of accepting the input. -/
  isComplete : String → Bool := fun _ => true
  /-- Syntax highlighting: styles for character ranges of the line. -/
  highlighter : Option (String → List Render.Span) := none

/-- Filename completion, no history file, automatic history. -/
def defaultSettings {m : Type → Type} [Monad m] [MonadLiftT IO m] : Settings m :=
  { complete := completeFilename }

def setComplete {m : Type → Type} [Monad m] (f : CompletionFunc m) (s : Settings m) : Settings m :=
  { s with complete := f }

/-- The outcome of reading a line. -/
inductive LineResult where
  | line (s : String)
  /-- End of input: Ctrl-D on an empty line, or end of file. -/
  | eof
  /-- Ctrl-C. -/
  | interrupted
  deriving DecidableEq, Repr, Inhabited

def LineResult.toOption : LineResult → Option String
  | .line s => some s
  | _ => none

/-! ## Sessions -/

structure Term where
  inFd : Terminal.Fd
  outFd : Terminal.Fd
  /-- The descriptor was opened by us and must be closed. -/
  owned : Bool
  reader : Reader
  /-- No cursor addressing (`TERM=dumb`): single-row, horizontally scrolling display. -/
  dumb : Bool := false

inductive Backend where
  | terminal (t : Term)
  | file (input : IO.FS.Stream)

/-- Messages from other threads waiting to be printed above the prompt. -/
structure ExternalState where
  editing : Bool := false
  queue : Array String := #[]
  deriving Inhabited

structure Session (m : Type → Type) [Monad m] where
  settings : Settings m
  prefs : Prefs
  backend : Backend
  history : IO.Ref History
  kill : IO.Ref KillRing
  external : IO.Ref ExternalState
  /-- Inside `withInterrupt`: Ctrl-C raises `interruptedError`. -/
  interruptible : IO.Ref Bool

/-- A monad transformer adding line editing to `m`. -/
def InputT (m : Type → Type) [Monad m] (α : Type) : Type := ReaderT (Session m) m α

namespace InputT

variable {m : Type → Type} [Monad m]

instance : Monad (InputT m) := inferInstanceAs (Monad (ReaderT (Session m) m))
instance : MonadLift m (InputT m) := inferInstanceAs (MonadLift m (ReaderT (Session m) m))
instance {ε : Type} [MonadExceptOf ε m] : MonadExceptOf ε (InputT m) :=
  inferInstanceAs (MonadExceptOf ε (ReaderT (Session m) m))
instance [MonadFinally m] : MonadFinally (InputT m) := inferInstanceAs (MonadFinally (ReaderT (Session m) m))
instance [Inhabited (m PUnit)] : Inhabited (InputT m PUnit) := ⟨fun _ => default⟩

def run {α : Type} (act : InputT m α) (s : Session m) : m α := ReaderT.run act s

def session : InputT m (Session m) := fun s => pure s

/-- Apply a transformation of the underlying monad (Haskeline's `mapInputT`). -/
def mapInputT {α : Type} (f : {β : Type} → m β → m β) (act : InputT m α) : InputT m α :=
  fun s => f (act.run s)

end InputT

export InputT (mapInputT)

section
variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadFinally m]

private def io {α : Type} (x : IO α) : InputT m α :=
  show ReaderT (Session m) m α from fun _ => (monadLift x : m α)

/-- The error raised by input functions for Ctrl-C inside `withInterrupt`. -/
def interruptedError : IO.Error := .interrupted "leanline" 0 "interrupted"

def isInterruptedError : IO.Error → Bool
  | .interrupted "leanline" _ _ => true
  | _ => false

private def flushStdout : IO Unit := do (← IO.getStdout).flush

private def writeTerm (t : Term) (s : String) : IO Unit := Terminal.writeString t.outFd s

private def termSize (t : Term) : IO Terminal.Size := do
  return (← Terminal.getSize? t.outFd).getD { cols := 80, rows := 24 }

private def editorConfig (ses : Session m) (password : Bool) : EditorConfig :=
  { editMode := ses.prefs.editMode
    completionType := ses.prefs.completionType
    listCompletionsImmediately := ses.prefs.listCompletionsImmediately
    bindings := ses.settings.keyBindings
    macros := ses.prefs.customBindings
    suggestions := ses.prefs.historySuggestions
    prefixHistorySearch := ses.prefs.prefixHistorySearch
    password
    isComplete := if password then (fun _ => true) else ses.settings.isComplete }

private def frameOf (ses : Session m) (prompt : String) (echo : Render.Echo) (v : Editor.View) : Render.Frame :=
  let gs := v.buf.before.reverse ++ v.buf.after
  let styles := match ses.settings.highlighter, echo with
    | some hl, .plain => Render.stylesFor gs (hl (stringOf gs))
    | _, _ => []
  { prompt := v.prompt.getD prompt, before := v.buf.before.reverse, after := v.buf.after,
    hint := v.hint, echo, styles }

/-- What is on the screen for the line being edited. -/
private structure Display where
  screen : Render.Screen := {}
  /-- Columns used by the last drawing on a dumb terminal. -/
  dumbUsed : Nat := 0
  deriving Inhabited

private def drawFrame (t : Term) (width : Nat) (d : Display) (f : Render.Frame) : IO Display := do
  if t.dumb then
    let (out, used) := Render.redrawDumb width d.dumbUsed f
    writeTerm t out
    return { d with dumbUsed := used }
  else
    let (out, screen) := Render.redraw width d.screen f
    writeTerm t out
    return { d with screen }

/-- Move to the line below the drawing. -/
private def leaveFrame (t : Term) (width : Nat) (d : Display) (f : Render.Frame) : IO Unit :=
  writeTerm t (if t.dumb then "\r\n" else Render.moveBelow width d.screen f)

/-- Erase the drawing, leaving the cursor where it started. -/
private def eraseFrame (t : Term) (d : Display) : IO Unit :=
  writeTerm t <| if t.dumb then "\r" ++ String.ofList (List.replicate d.dumbUsed ' ') ++ "\r"
    else Render.cursorUp d.screen.cursorRow ++ "\r" ++ Render.clearToEnd

private def ringBell (ses : Session m) (t : Term) : IO Unit :=
  match ses.prefs.bellStyle with
  | .none => pure ()
  | .audible => writeTerm t "\x07"
  | .visual => do
    writeTerm t "\x1b[?5h"
    IO.sleep 100
    writeTerm t "\x1b[?5l"

/-- Take the queued external messages. -/
private def takeMessages (ses : Session m) : IO (Array String) :=
  ses.external.modifyGet fun e => (e.queue, { e with queue := #[] })

private def enterRaw (ses : Session m) (t : Term) : IO Unit := do
  flushStdout
  Terminal.enableRawMode t.inFd
  Terminal.installResizeHandler
  if !t.dumb then writeTerm t "\x1b[?2004h"
  ses.external.modify fun e => { e with editing := true }

private def leaveRaw (ses : Session m) (t : Term) : IO Unit := do
  if !t.dumb then writeTerm t "\x1b[?2004l"
  Terminal.disableRawMode t.inFd
  Terminal.uninstallResizeHandler
  ses.external.modify fun e => { e with editing := false }
  for msg in ← takeMessages ses do
    writeTerm t (msg ++ "\n")

/-- Run `act` with the terminal in raw mode, restoring it afterwards. -/
private def withRaw {α : Type} (ses : Session m) (t : Term) (act : InputT m α) : InputT m α := do
  io (enterRaw ses t)
  tryFinally act (io (leaveRaw ses t))

private partial def readYesNo (t : Term) : IO Bool := do
  match ← t.reader.nextEvent with
  | some (.key k) =>
    match k.printable? with
    | some 'y' | some 'Y' | some ' ' => return true
    | some 'n' | some 'N' | some 'q' => return false
    | _ =>
      if k == .plain .escape || k == Key.ctrl 'c' || k == Key.ctrl 'g' || k == .plain .enter then return false
      else readYesNo t
  | some (.paste _) => readYesNo t
  | none => return false

/-- Ask a yes/no question on the terminal. -/
private def askYesNo (t : Term) (question : String) : IO Bool := do
  writeTerm t question
  let answer ← readYesNo t
  writeTerm t "\r\n"
  return answer

/-- Print completion candidates in columns below the input, paging if needed. -/
private def showListing (ses : Session m) (t : Term) (items : List String) : IO Unit := do
  let size ← termSize t
  let proceed ← match ses.prefs.completionPromptLimit with
    | some lim =>
      if items.length > lim then askYesNo t s!"Display all {items.length} possibilities? (y or n)"
      else pure true
    | none => pure true
  if !proceed then return
  let rows := Render.columns size.cols items
  let pageSize := max 1 (size.rows - 1)
  if !ses.prefs.completionPaging || rows.length ≤ pageSize then
    for r in rows do writeTerm t (r ++ "\r\n")
  else
    let mut remaining := rows
    let mut budget := pageSize
    while !remaining.isEmpty do
      for r in remaining.take budget do writeTerm t (r ++ "\r\n")
      remaining := remaining.drop budget
      if remaining.isEmpty then break
      writeTerm t "--More--"
      let k ← t.reader.nextEvent
      writeTerm t "\r\x1b[K"
      match k with
      | some (.key k) =>
        if k == .plain .enter || k.printable? == some 'j' then budget := 1
        else if k.printable? == some ' ' then budget := pageSize
        else remaining := []
      | _ => remaining := []

/-- Edit `path` with `$VISUAL`, `$EDITOR` or `vi`, returning the new contents. -/
private def runExternalEditor (text : String) : IO (Option String) := do
  let editor := (← IO.getEnv "VISUAL").getD ((← IO.getEnv "EDITOR").getD "vi")
  let words := (editor.splitOn " ").filter (· != "")
  let (cmd, args) := match words with
    | c :: as => (c, as)
    | [] => ("vi", [])
  let (h, path) ← IO.FS.createTempFile
  h.putStr (text ++ "\n")
  h.flush
  try
    let child ← IO.Process.spawn { cmd, args := (args ++ [path.toString]).toArray,
                                   stdin := .inherit, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    if code != 0 then return none
    let contents ← IO.FS.readFile path
    let contents := if contents.endsWith "\n" then String.ofList contents.toList.dropLast else contents
    return some contents
  finally
    try IO.FS.removeFile path catch _ => pure ()

/-- The interactive editor loop. -/
private def termReadLine (ses : Session m) (t : Term) (prompt : String) (cfg : EditorConfig)
    (echo : Render.Echo) (init : LineBuffer) : InputT m LineResult := withRaw ses t do
  let hist ← io ses.history.get
  let kill ← io ses.kill.get
  let mut st := Editor.initial cfg hist.entries (if cfg.password then {} else kill) init
  let mut disp : Display := {}
  let mut size ← io (termSize t)
  let frame := fun (st : EditorState) => frameOf ses prompt echo (Editor.view cfg st)
  -- Draw the final state without hints (followed by `suffix`) and move below it.
  let finish := fun (st : EditorState) (disp : Display) (width : Nat) (suffix : String) =>
    io (m := m) do
      let f := frameOf ses prompt echo { Editor.view cfg { st with overlay := .none } with hint := [] }
      let f := if suffix.isEmpty then f else { f with before := f.before ++ f.after, after := [] }
      let disp ← drawFrame t width disp f
      writeTerm t suffix
      leaveFrame t width disp f
  disp ← io (drawFrame t size.cols disp (frame st))
  repeat
    let msgs ← io (takeMessages ses)
    if !msgs.isEmpty then
      io (eraseFrame t disp)
      io (writeTerm t (String.join (msgs.toList.map (· ++ "\r\n"))))
      disp ← io (drawFrame t size.cols {} (frame st))
    match ← io t.reader.next with
    | .resized =>
      size ← io (termSize t)
      disp ← io (drawFrame t size.cols { disp with screen := Render.resize size.cols disp.screen } (frame st))
    | .woken => pure ()
    | .eof =>
      finish st disp size.cols ""
      return .eof
    | .event ev =>
      let mut r := Editor.handleEvent cfg st ev
      repeat
        st := r.state
        for eff in r.effects do
          match eff with
          | .bell => io (ringBell ses t)
          | .clearScreen =>
            io (writeTerm t (if t.dumb then "\r\n" else "\x1b[H\x1b[2J"))
            disp := {}
          | .listCompletions items =>
            io (leaveFrame t size.cols disp (frame st))
            io (showListing ses t items)
            disp := {}
          | .suspend =>
            io (leaveFrame t size.cols disp (frame st))
            io (leaveRaw ses t)
            io (Terminal.suspend t.inFd)
            io (enterRaw ses t)
            size ← io (termSize t)
            disp := {}
          | .editInEditor =>
            io (leaveFrame t size.cols disp (frame st))
            io (leaveRaw ses t)
            let edited ← io (runExternalEditor st.buf.toString)
            io (enterRaw ses t)
            if let some text := edited then st := Editor.replaceLine text st
            size ← io (termSize t)
            disp := {}
        match r.status with
        | .editing => break
        | .complete kind =>
          let req : CompletionRequest := { before := st.buf.textBefore, after := st.buf.textAfter }
          let res ← (liftM (ses.settings.complete req) : InputT m CompletionResult)
          r := Editor.applyCompletion cfg kind res st
        | .accept line =>
          finish st disp size.cols ""
          if !cfg.password then io (ses.kill.set st.kill)
          return .line line
        | .eof =>
          finish st disp size.cols ""
          return .eof
        | .interrupt =>
          finish st disp size.cols "^C"
          return .interrupted
      if !(← io t.reader.hasBuffered) then
        disp ← io (drawFrame t size.cols disp (frame st))
  return .eof

private def stripNewline (s : String) : String :=
  let cs := s.toList
  let cs := if cs.getLast? == some '\n' then cs.dropLast else cs
  let cs := if cs.getLast? == some '\r' then cs.dropLast else cs
  String.ofList cs

private def fileReadLine (input : IO.FS.Stream) (prompt : String) : IO (Option String) := do
  let out ← IO.getStdout
  out.putStr prompt
  out.flush
  let line ← input.getLine
  if line.isEmpty then return none
  return some (stripNewline line)

/-- Read a line and keep reading continuation lines while `isComplete` fails. -/
private partial def fileReadInput (input : IO.FS.Stream) (prompt : String) (isComplete : String → Bool) :
    IO (Option String) := do
  match ← fileReadLine input prompt with
  | none => return none
  | some first =>
    let rec more (acc : String) : IO String := do
      if isComplete acc then return acc
      match ← fileReadLine input "" with
      | some next => more (acc ++ "\n" ++ next)
      | none => return acc
    return some (← more first)

/-- Read a line from a stream and return its first character (`\n` for an
empty line), mirroring a single key press on a terminal. -/
private def fileReadChar (input : IO.FS.Stream) : IO (Option Char) := do
  let line ← input.getLine
  if line.isEmpty then return none
  return some ((stripNewline line).toList.head?.getD '\n')

private def addToHistory (ses : Session m) (line : String) : IO Unit := do
  if ses.settings.autoAddHistory && !line.all Unicode.isSpace then
    ses.history.modify (·.addWith ses.prefs.historyDuplicates line)

private def throwIfInterruptible (ses : Session m) : InputT m Unit := do
  if ← io ses.interruptible.get then io (throw interruptedError)

/-- Read a line; Ctrl-C is reported as `interrupted`. -/
def getInputLineResultWithInitial (prompt : String) (initial : String × String) : InputT m LineResult := do
  let ses ← InputT.session
  match ses.backend with
  | .terminal t =>
    let r ← termReadLine ses t prompt (editorConfig ses false) .plain (LineBuffer.ofParts initial.1 initial.2)
    if let .line s := r then io (addToHistory ses s)
    return r
  | .file input =>
    match ← io (fileReadInput input prompt ses.settings.isComplete) with
    | some s =>
      io (addToHistory ses s)
      return .line s
    | none => return .eof

/-- Read a line; Ctrl-C is reported as `interrupted`. -/
def getInputLineResult (prompt : String) : InputT m LineResult :=
  getInputLineResultWithInitial prompt ("", "")

/-- Read a line of input with `initial` already typed (the cursor sits
between its two parts). Returns `none` at end of input. Ctrl-C discards the
line and starts over on a new one, or raises `interruptedError` inside
`withInterrupt`. -/
def getInputLineWithInitial (prompt : String) (initial : String × String) : InputT m (Option String) := do
  let ses ← InputT.session
  if (← io ses.interruptible.get) && (← io Terminal.takeSigint) then io (throw interruptedError)
  repeat
    match ← getInputLineResultWithInitial prompt initial with
    | .line s => return some s
    | .eof => return none
    | .interrupted => throwIfInterruptible ses
  return none

/-- Read a line of input. Returns `none` at end of input (Ctrl-D on an empty
line, or end of file). -/
def getInputLine (prompt : String) : InputT m (Option String) :=
  getInputLineWithInitial prompt ("", "")

/-- Read a password. With `mask := some '*'` each character is echoed as `*`;
with `none` nothing is echoed. The line is not added to the history, and
completion, history and the kill ring are unavailable while typing it. -/
def getPassword (mask : Option Char) (prompt : String) : InputT m (Option String) := do
  let ses ← InputT.session
  match ses.backend with
  | .terminal t =>
    let echo := match mask with
      | some c => Render.Echo.mask c
      | none => .hidden
    repeat
      match ← termReadLine ses t prompt (editorConfig ses true) echo {} with
      | .line s => return some s
      | .eof => return none
      | .interrupted => throwIfInterruptible ses
    return none
  | .file input => io (fileReadLine input prompt)

/-- Read a single printable character (echoed, followed by a newline).
Returns `none` on Ctrl-D or end of input. Ctrl-C asks again, or raises
`interruptedError` inside `withInterrupt`. -/
def getInputChar (prompt : String) : InputT m (Option Char) := do
  let ses ← InputT.session
  match ses.backend with
  | .file input =>
    io do
      let out ← IO.getStdout
      out.putStr prompt
      out.flush
    io (fileReadChar input)
  | .terminal t =>
    repeat
      -- `none` means Ctrl-C; `some r` is the answer.
      let r : Option (Option Char) ← withRaw ses t do
        io (writeTerm t prompt)
        repeat
          match ← io t.reader.next with
          | .event (.key k) =>
            if k == Key.ctrl 'd' then
              io (writeTerm t "\r\n")
              return some none
            if k == Key.ctrl 'c' then
              io (writeTerm t "^C\r\n")
              return none
            let c? := if k == .plain .enter || k == Key.ctrl 'j' then some '\n' else k.printable?
            match c? with
            | some c =>
              io (writeTerm t ((if c == '\n' then "" else c.toString) ++ "\r\n"))
              return some (some c)
            | none => io (ringBell ses t)
          | .event (.paste text) =>
            if let some c := text.toList.head? then
              io (writeTerm t (c.toString ++ "\r\n"))
              return some (some c)
          | .eof =>
            io (writeTerm t "\r\n")
            return some none
          | _ => pure ()
        return some none
      match r with
      | some c => return c
      | none => throwIfInterruptible ses
    return none

/-- Wait for any key. Returns `false` on Ctrl-D or end of input. -/
def waitForAnyKey (prompt : String) : InputT m Bool := do
  let ses ← InputT.session
  match ses.backend with
  | .file input =>
    io do
      let out ← IO.getStdout
      out.putStr prompt
      out.flush
    return (← io (fileReadChar input)).isSome
  | .terminal t =>
    withRaw ses t do
      io (writeTerm t prompt)
      repeat
        match ← io t.reader.next with
        | .event (.key k) =>
          io (writeTerm t "\r\n")
          if k == Key.ctrl 'c' then throwIfInterruptible ses
          return k != Key.ctrl 'd'
        | .event (.paste _) =>
          io (writeTerm t "\r\n")
          return true
        | .eof =>
          io (writeTerm t "\r\n")
          return false
        | _ => pure ()
      return false

/-- Write a string to the user's output. -/
def outputStr (s : String) : InputT m Unit := do
  let ses ← InputT.session
  match ses.backend with
  | .terminal t => io do
    flushStdout
    writeTerm t s
  | .file _ => io do
    let out ← IO.getStdout
    out.putStr s
    out.flush

def outputStrLn (s : String) : InputT m Unit := outputStr (s ++ "\n")

/-- A function that other threads can use to print a line while input is
being edited. The line appears above the prompt, which is redrawn below it. -/
def getExternalPrint : InputT m (String → IO Unit) := do
  let ses ← InputT.session
  return fun msg => do
    let msg := if msg.endsWith "\n" then String.ofList msg.toList.dropLast else msg
    let printNow ← ses.external.modifyGet fun e =>
      if e.editing then (false, { e with queue := e.queue.push msg }) else (true, e)
    if printNow then
      match ses.backend with
      | .terminal t => writeTerm t (msg ++ "\n")
      | .file _ => do
        let out ← IO.getStdout
        out.putStrLn msg
        out.flush
    else Terminal.wake

/-- Is input coming from an interactive terminal? -/
def haveTerminalUI : InputT m Bool := do
  match (← InputT.session).backend with
  | .terminal _ => return true
  | .file _ => return false

def getHistory : InputT m History := do io (← InputT.session).history.get
def putHistory (h : History) : InputT m Unit := do io ((← InputT.session).history.set h)
def modifyHistory (f : History → History) : InputT m Unit := do io ((← InputT.session).history.modify f)

/-- The preferences in effect. -/
def getPrefs : InputT m Prefs := return (← InputT.session).prefs

/-! ## Interrupts

Inside `withInterrupt`, Ctrl-C at a prompt raises `interruptedError`, and so
does `checkInterrupt` if SIGINT arrived while the program was busy (instead
of the process being killed). `handleInterrupt` catches the error. -/

def withInterrupt {α : Type} (act : InputT m α) : InputT m α := do
  let ses ← InputT.session
  let prev ← io ses.interruptible.get
  io do
    ses.interruptible.set true
    Terminal.installSigintHandler
  tryFinally act <| io do
    ses.interruptible.set prev
    if !prev then Terminal.uninstallSigintHandler

/-- Raise `interruptedError` if SIGINT arrived since the last check. -/
def checkInterrupt : InputT m Unit := do
  if ← io Terminal.takeSigint then io (throw interruptedError)

/-- Run `act`; if it raises `interruptedError`, run `handler` instead. -/
def handleInterrupt {α : Type} [MonadExceptOf IO.Error m] (handler : InputT m α) (act : InputT m α) : InputT m α :=
  tryCatchThe IO.Error act fun e => if isInterruptedError e then handler else throwThe IO.Error e

/-! ## Running -/

private def openBackend (behavior : Behavior) (prefs : Prefs) : IO (Backend × IO Unit) := do
  Terminal.init
  let term ← IO.getEnv "TERM"
  let table := prefs.keySeqTable term
  let dumb := term == some "dumb" || term == some ""
  let stdinBackend : IO (Backend × IO Unit) := do
    if (← Terminal.isTerminal .stdin) && (← Terminal.isTerminal .stdout) then
      let reader ← Reader.create .stdin table prefs.keySeqTimeout
      return (.terminal { inFd := .stdin, outFd := .stdout, owned := false, reader, dumb }, pure ())
    return (.file (← IO.getStdin), pure ())
  match behavior with
  | .defaultBehavior => stdinBackend
  | .useStream s => return (.file s, pure ())
  | .useFile path =>
    let h ← IO.FS.Handle.mk path .read
    return (.file (IO.FS.Stream.ofHandle h), pure ())
  | .preferTerm =>
    try
      let fd ← Terminal.openControllingTerminal
      let reader ← Reader.create fd table prefs.keySeqTimeout
      return (.terminal { inFd := fd, outFd := fd, owned := true, reader, dumb }, Terminal.close fd)
    catch _ => stdinBackend

/-- Run with explicit behaviour and preferences. -/
def runInputTBehaviorWithPrefs {α : Type} (behavior : Behavior) (prefs : Prefs) (settings : Settings m)
    (act : InputT m α) : m α := do
  let lift {β : Type} (x : IO β) : m β := monadLift x
  let (backend, cleanup) ← lift (openBackend behavior prefs)
  let hist ← lift <| match settings.historyFile with
    | some path => History.readFile path prefs.maxHistorySize
    | none => pure { maxSize := prefs.maxHistorySize }
  let ses : Session m :=
    { settings, prefs, backend
      history := ← lift (IO.mkRef hist)
      kill := ← lift (IO.mkRef {})
      external := ← lift (IO.mkRef {})
      interruptible := ← lift (IO.mkRef false) }
  tryFinally (act.run ses) <| lift do
    if let some path := settings.historyFile then
      try (← ses.history.get).writeFile path catch _ => pure ()
    cleanup

/-- Run with preferences read from `~/.leanline`. -/
def runInputTBehavior {α : Type} (behavior : Behavior) (settings : Settings m) (act : InputT m α) : m α := do
  let prefs ← (monadLift (do
    match ← Prefs.defaultPath with
    | some p => Prefs.readFile p
    | none => pure {} : IO Prefs) : m Prefs)
  runInputTBehaviorWithPrefs behavior prefs settings act

def runInputTWithPrefs {α : Type} (prefs : Prefs) (settings : Settings m) (act : InputT m α) : m α :=
  runInputTBehaviorWithPrefs .defaultBehavior prefs settings act

/-- Run an `InputT` computation with the default behaviour and the user's
preferences from `~/.leanline`. -/
def runInputT {α : Type} (settings : Settings m) (act : InputT m α) : m α :=
  runInputTBehavior .defaultBehavior settings act

end

/-- Read the user's preferences file (`~/.leanline` by default). -/
def readPrefs (path : Option System.FilePath := none) : IO Prefs := do
  match path with
  | some p => Prefs.readFile p
  | none =>
    match ← Prefs.defaultPath with
    | some p => Prefs.readFile p
    | none => return {}

end Leanline
