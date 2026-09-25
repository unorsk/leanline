import Leanline.Editor.Keymaps

/-!
# Editor core

Execution of `Command`s, incremental search, and completion results. Vi
command mode builds on these in `Leanline.Editor.Vi`.
-/

namespace Leanline.Editor

/-- A fresh editing state for one line of input. -/
def initial (cfg : EditorConfig) (history : List String) (kill : KillRing := {})
    (buf : LineBuffer := {}) : EditorState :=
  let history := if cfg.password then [] else history
  { buf, original := buf, nav := { older := history }, history, kill,
    mode := match cfg.editMode with
      | .emacs => .emacs
      | .vi => .vi .insert }

def ok (s : EditorState) : StepResult := { state := s }
def bell (s : EditorState) : StepResult := { state := s, effects := [.bell] }

/-! ## Helpers -/

/-- First index at which `needle` occurs in `hay`. -/
def findSub (hay needle : List Char) : Option Nat :=
  go hay 0
where
  go : List Char → Nat → Option Nat
    | [], i => if needle.isEmpty then some i else none
    | l@(_ :: rest), i => if needle.isPrefixOf l then some i else go rest (i + 1)

/-- Grapheme index of the grapheme containing character index `i`. -/
def graphemeIndexOfChar (gs : List Grapheme) (i : Nat) : Nat :=
  go gs 0 0
where
  go : List Grapheme → Nat → Nat → Nat
    | [], _, gi => gi
    | g :: rest, ci, gi => if ci + g.toList.length > i then gi else go rest (ci + g.toList.length) (gi + 1)

/-- A buffer holding `line` with the cursor at character index `i`. -/
def bufferAt (line : String) (i : Nat) : LineBuffer :=
  let gs := graphemesOf line
  let gi := graphemeIndexOfChar gs i
  LineBuffer.ofLists (gs.take gi) (gs.drop gi)

/-- The character a key produces when inserted literally (`C-v`). -/
def literalChar (k : Key) : Option Char :=
  match k.base with
  | .char c => if k.mods.ctrl then some (Char.ofNat (c.toNat % 32)) else some c
  | .enter => some '\r'
  | .tab => some '\t'
  | .escape => some '\x1b'
  | .backspace => some '\x7f'
  | _ => none

/-- Last whitespace-separated word of a line. -/
def lastWord (line : String) : Option String :=
  (line.splitOn " ").reverse.find? (· != "")

/-- The history suggestion shown after the cursor, if any. -/
def suggestion (cfg : EditorConfig) (s : EditorState) : Option (List Grapheme) :=
  if !cfg.suggestions || cfg.password || s.overlay != .none || !s.buf.atEnd || s.buf.isEmpty then none
  else
    let text := s.buf.toString
    match s.history.find? (fun e => text.isPrefixOf e && e != text) with
    | some e => some ((graphemesOf e).drop s.buf.length)
    | none => none

/-- Commands that replace the line from history; they do not create undo steps. -/
def replacesFromHistory : Command → Bool
  | .previousHistory | .nextHistory | .beginningOfHistory | .endOfHistory
  | .historySearchBackward | .historySearchForward
  | .reverseSearchHistory | .forwardSearchHistory => true
  | _ => false

/-- Record an undo step if `cmd` changed the buffer. Consecutive insertions
(and everything typed in one vi insert session) form a single step. -/
def recordUndo (cmd : Command) (before : EditorState) (r : StepResult) : StepResult :=
  let st := r.state
  if cmd == .undo || cmd == .redo then r
  else if replacesFromHistory cmd then { r with state := { st with undoGroup := false } }
  else if st.buf.graphemes == before.buf.graphemes then
    if cmd == .selfInsert then r else { r with state := { st with undoGroup := st.undoGroup && st.mode == .vi .insert } }
  else
    let grouped := before.undoGroup && (cmd == .selfInsert || st.mode == .vi .insert)
    let st := if grouped then st
      else { st with undoStack := before.buf :: st.undoStack, redoStack := [] }
    { r with state := { st with undoGroup := cmd == .selfInsert || st.mode == .vi .insert } }

/-- Kill the region between the cursor and where `motion` would move it. -/
def killMotion (cfg : EditorConfig) (motion : LineBuffer → LineBuffer) (backward : Bool)
    (prev : LastAction) (s : EditorState) : EditorState :=
  let (b, text) := s.buf.deleteMotion motion
  let kill :=
    if cfg.password then s.kill
    else match prev with
      | .kill _ => s.kill.merge text backward
      | _ => s.kill.push text
  { s with buf := b, kill, last := .kill backward }

/-! ## Incremental search -/

def searchPrompt (ss : SearchState) : String :=
  (if ss.failed then "(failed " else "(") ++ (if ss.backward then "reverse-i-search)`" else "i-search)`") ++
  String.ofList ss.query ++ "': "

/-- Search for `ss.query`, starting with the current line unless `skipCurrent`. -/
def searchStep (s : EditorState) (ss : SearchState) (skipCurrent : Bool) : StepResult :=
  let q := ss.query
  let current := s.buf.toString
  let s := { s with lastSearchQuery := if q.isEmpty then s.lastSearchQuery else q }
  if q.isEmpty then ok { s with overlay := .isearch { ss with failed := false } }
  else match (if skipCurrent then none else findSub current.toList q) with
    | some i => ok { s with buf := bufferAt current i, overlay := .isearch { ss with failed := false } }
    | none =>
      let hits (e : String) := (findSub e.toList q).isSome
      let found := if ss.backward then s.nav.backUntil hits current else s.nav.forwardUntil hits current
      match found with
      | some (e, nav) =>
        ok { s with buf := bufferAt e ((findSub e.toList q).getD 0), nav,
                    overlay := .isearch { ss with failed := false } }
      | none => bell { s with overlay := .isearch { ss with failed := true } }

/-! ## Completion -/

/-- Replace the text before the cursor by `kept ++ ins`. -/
private def withBefore (kept ins : List Grapheme) (s : EditorState) : LineBuffer :=
  LineBuffer.ofLists (kept ++ ins) s.buf.after

def completionText (c : Completion) : List Grapheme :=
  graphemesOf c.replacement ++ (if c.isFinished then [Grapheme.ofChar ' '] else [])

/-- Apply the result of the completion function requested by `Status.complete`. -/
def applyCompletion (cfg : EditorConfig) (kind : CompletionKind) (res : CompletionResult)
    (s : EditorState) : StepResult :=
  let prev := s.last
  let s := { s with last := .complete, undoGroup := false }
  let before := s.buf.textBefore
  let kept := graphemesOf res.kept
  let word : List Char := if res.kept.isPrefixOf before then before.toList.drop res.kept.length else []
  let displays := res.candidates.map (·.display)
  let withUndo (b : LineBuffer) : EditorState :=
    if b == s.buf then s else { s with buf := b, undoStack := s.buf :: s.undoStack, redoStack := [] }
  match kind, res.candidates with
  | _, [] => bell s
  | .listOnly, _ => { state := s, effects := [.listCompletions displays] }
  | _, [c] => ok (withUndo (withBefore kept (completionText c) s))
  | .menu backward, cs =>
    let idx := if backward then cs.length - 1 else 0
    let rep := (cs[idx]?.map (·.replacement)).getD ""
    let st := withUndo (withBefore kept (graphemesOf rep) s)
    ok { st with overlay := .menu { kept, after := s.buf.after, candidates := cs, index := idx, original := s.buf } }
  | .insert, cs =>
    let lcp := longestCommonPrefix (cs.map (·.replacement.toList))
    if lcp.length > word.length then ok (withUndo (withBefore kept (graphemes lcp) s))
    else if cfg.listCompletionsImmediately || prev == .complete then
      { state := s, effects := [.listCompletions displays] }
    else bell s

/-- Show the menu entry `i` (`candidates.length` means the original text). -/
def menuShow (ms : MenuState) (i : Nat) : LineBuffer :=
  match ms.candidates[i]? with
  | some c => LineBuffer.ofLists (ms.kept ++ graphemesOf c.replacement) ms.after
  | none => ms.original

/-! ## Commands -/

/-- Leave vi insert or replace mode for command mode. -/
def enterViCommand (s : EditorState) : EditorState :=
  let lastChange := match s.vi.recording with
    | some ch => some ch
    | none => s.vi.lastChange
  { s with mode := .vi .command, buf := s.buf.moveLeft, undoGroup := false, pending := [],
           vi := { s.vi with recording := none, lastChange } }

/-- Append to (or remove from) the text recorded for vi `.` repetition. -/
def recordInsert (f : List Grapheme → List Grapheme) (s : EditorState) : EditorState :=
  match s.vi.recording with
  | some ch => { s with vi := { s.vi with recording := some { ch with inserted := f ch.inserted } } }
  | none => s

def histBack (s : EditorState) : Option EditorState :=
  (s.nav.back s.buf.toString).map fun (e, nav) => { s with buf := LineBuffer.ofString e, nav }

def histForward (s : EditorState) : Option EditorState :=
  (s.nav.forward s.buf.toString).map fun (e, nav) => { s with buf := LineBuffer.ofString e, nav }

def repeatOpt (n : Nat) (f : EditorState → Option EditorState) (s : EditorState) : Option EditorState :=
  match n with
  | 0 => some s
  | n + 1 => (f s).bind (repeatOpt n f)

/-- Prefix history search (`M-p` / `M-n`), keeping the original prefix across repeats. -/
def prefixSearch (backward : Bool) (prev : LastAction) (s : EditorState) : StepResult :=
  let pfx := match prev with
    | .prefixSearch p => p
    | _ => s.buf.before.reverse
  let pfxChars := charsOf pfx
  let current := s.buf.toString
  let p (e : String) := pfxChars.isPrefixOf e.toList && e != current
  let found := if backward then s.nav.backUntil p current else s.nav.forwardUntil p current
  match found with
  | some (e, nav) => ok { s with buf := LineBuffer.ofString e, nav, last := .prefixSearch pfx }
  | none =>
    -- Searching forward past the newest match returns to the typed prefix.
    if !backward && !s.nav.newer.isEmpty then
      let (_, nav) := s.nav.toNewest current
      ok { s with buf := LineBuffer.ofLists pfx [], nav, last := .prefixSearch pfx }
    else { state := { s with last := .prefixSearch pfx }, effects := [.bell] }

/-- Execute one command. `key` is the key that invoked it (for `selfInsert`). -/
def exec (cfg : EditorConfig) (cmd : Command) (key : Key) (s0 : EditorState) : StepResult :=
  let n := s0.arg.getD 1
  let prev := s0.last
  let s := { s0 with arg := none, pending := [], last := .other }
  let viInsert := s.mode == .vi .insert
  match cmd with
  | .selfInsert =>
    match key.printable? with
    | some c =>
      if s.mode == .vi .replace then
        let b := LineBuffer.iterate n (fun b => if b.atEnd then b.insertChar c else (b.replaceCurrent c).moveRight) s.buf
        ok { s with buf := b, last := .insert }
      else
        let s := { s with buf := LineBuffer.iterate n (·.insertChar c) s.buf, last := .insert }
        ok (recordInsert (· ++ List.replicate n (Grapheme.ofChar c)) s)
    | none => bell s
  | .insertText t =>
    ok (recordInsert (· ++ graphemesOf t) { s with buf := s.buf.insertString t })
  | .quotedInsert => ok { s with overlay := .quoted, arg := s0.arg }
  | .newline => ok (recordInsert (· ++ [Grapheme.ofChar '\n']) { s with buf := s.buf.insertChar '\n' })
  | .forwardChar =>
    match (if s.buf.atEnd then suggestion cfg s else none) with
    | some hint => ok { s with buf := s.buf.insertList hint }
    | none => ok { s with buf := LineBuffer.iterate n LineBuffer.moveRight s.buf }
  | .backwardChar => ok { s with buf := LineBuffer.iterate n LineBuffer.moveLeft s.buf }
  | .forwardWord => ok { s with buf := LineBuffer.iterate n LineBuffer.wordRight s.buf }
  | .backwardWord => ok { s with buf := LineBuffer.iterate n LineBuffer.wordLeft s.buf }
  | .beginningOfLine => ok { s with buf := s.buf.moveToStart }
  | .endOfLine =>
    match (if s.buf.atEnd then suggestion cfg s else none) with
    | some hint => ok { s with buf := s.buf.insertList hint }
    | none => ok { s with buf := s.buf.moveToEnd }
  | .deleteChar => ok { s with buf := LineBuffer.iterate n LineBuffer.deleteForward s.buf }
  | .backwardDeleteChar =>
    if s.buf.atStart then bell s
    else ok (recordInsert (·.dropLast) { s with buf := LineBuffer.iterate n LineBuffer.deleteBackward s.buf })
  | .deleteCharOrEof =>
    if s.buf.isEmpty then { state := s, status := .eof }
    else if s.buf.atEnd then (if viInsert then bell s else ok s)
    else ok { s with buf := LineBuffer.iterate n LineBuffer.deleteForward s.buf }
  | .killLine => ok (killMotion cfg LineBuffer.moveToEnd false prev s)
  | .backwardKillLine => ok (killMotion cfg LineBuffer.moveToStart true prev s)
  | .killWholeLine => ok (killMotion cfg LineBuffer.moveToEnd false prev { s with buf := s.buf.moveToStart })
  | .killWord => ok (killMotion cfg (LineBuffer.iterate n LineBuffer.wordRight) false prev s)
  | .backwardKillWord => ok (killMotion cfg (LineBuffer.iterate n LineBuffer.wordLeft) true prev s)
  | .unixWordRubout => ok (killMotion cfg (LineBuffer.iterate n LineBuffer.bigWordLeft) true prev s)
  | .yank =>
    match s.kill.top? with
    | some t => ok { s with buf := s.buf.insertList t, last := .yank t.length }
    | none => bell s
  | .yankPop =>
    match prev with
    | .yank len =>
      let kill := s.kill.rotate
      let t := kill.top?.getD []
      let b := (LineBuffer.iterate len LineBuffer.deleteBackward s.buf).insertList t
      ok { s with buf := b, kill, last := .yank t.length }
    | _ => bell s
  | .yankLastArg =>
    let (idx, len) := match prev with
      | .yankLastArg i l => (i + 1, l)
      | _ => (0, 0)
    match s.history[idx]?.bind lastWord with
    | some w =>
      let g := graphemesOf w
      ok { s with buf := (LineBuffer.iterate len LineBuffer.deleteBackward s.buf).insertList g,
                  last := .yankLastArg idx g.length }
    | none => bell { s with last := prev }
  | .transposeChars =>
    let b := s.buf.transpose
    if b == s.buf then bell s else ok { s with buf := b }
  | .upcaseWord => ok { s with buf := LineBuffer.iterate n LineBuffer.upcaseWord s.buf }
  | .downcaseWord => ok { s with buf := LineBuffer.iterate n LineBuffer.downcaseWord s.buf }
  | .capitalizeWord => ok { s with buf := LineBuffer.iterate n LineBuffer.capitalizeWord s.buf }
  | .previousHistory =>
    if let some b := s.buf.lineUp? then ok { s with buf := b }
    else if cfg.prefixHistorySearch then prefixSearch true prev s
    else match repeatOpt n histBack s with
      | some s' => ok s'
      | none => bell s
  | .nextHistory =>
    if let some b := s.buf.lineDown? then ok { s with buf := b }
    else if cfg.prefixHistorySearch then prefixSearch false prev s
    else match repeatOpt n histForward s with
      | some s' => ok s'
      | none => bell s
  | .beginningOfHistory =>
    let (e, nav) := s.nav.toOldest s.buf.toString
    ok { s with buf := LineBuffer.ofString e, nav }
  | .endOfHistory =>
    let (e, nav) := s.nav.toNewest s.buf.toString
    ok { s with buf := LineBuffer.ofString e, nav }
  | .historySearchBackward => prefixSearch true prev s
  | .historySearchForward => prefixSearch false prev s
  | .reverseSearchHistory =>
    if cfg.password then bell s
    else ok { s with overlay := .isearch { backward := true, query := [], savedBuf := s.buf, savedNav := s.nav } }
  | .forwardSearchHistory =>
    if cfg.password then bell s
    else ok { s with overlay := .isearch { backward := false, query := [], savedBuf := s.buf, savedNav := s.nav } }
  | .complete =>
    if !cfg.hasCompletion || cfg.password then bell s
    else { state := { s with last := prev },
           status := .complete (if cfg.completionType == .menu then .menu false else .insert) }
  | .menuComplete =>
    if !cfg.hasCompletion || cfg.password then bell s
    else { state := { s with last := prev }, status := .complete (.menu false) }
  | .menuCompleteBackward =>
    if !cfg.hasCompletion || cfg.password then bell s
    else { state := { s with last := prev }, status := .complete (.menu true) }
  | .possibleCompletions =>
    if !cfg.hasCompletion || cfg.password then bell s
    else { state := { s with last := prev }, status := .complete .listOnly }
  | .undo =>
    match s.undoStack with
    | b :: rest => ok { s with buf := b, undoStack := rest, redoStack := s.buf :: s.redoStack, undoGroup := false }
    | [] => bell s
  | .redo =>
    match s.redoStack with
    | b :: rest => ok { s with buf := b, redoStack := rest, undoStack := s.buf :: s.undoStack, undoGroup := false }
    | [] => bell s
  | .revertLine => ok { s with buf := s.original }
  | .acceptLine =>
    let text := s.buf.toString
    if cfg.isComplete text then { state := s, status := .accept text }
    else ok (recordInsert (· ++ [Grapheme.ofChar '\n']) { s with buf := s.buf.insertChar '\n' })
  | .interrupt => { state := s, status := .interrupt }
  | .clearScreen => { state := s, effects := [.clearScreen] }
  | .suspend => { state := s, effects := [.suspend] }
  | .editInEditor => if cfg.password then bell s else { state := s, effects := [.editInEditor] }
  | .digitArgument d => ok { s with arg := some ((s0.arg.getD 0) * 10 + d), last := prev }
  | .abort => bell s
  | .viCommandMode => ok (enterViCommand s)
  | .bell => bell s
  | .noop => ok s

/-- Execute a command and record undo information. -/
def runCommand (cfg : EditorConfig) (cmd : Command) (key : Key) (s : EditorState) : StepResult :=
  recordUndo cmd s (exec cfg cmd key s)

/-- Look `keys` up in the user bindings, then in `km`. -/
def lookupKeys (cfg : EditorConfig) (km : Keymap) (keys : List Key) : KeymapLookup :=
  (cfg.bindings ++ km).lookup keys

/-- Handle a key with a keymap (Emacs mode and vi insert mode). -/
def keymapKey (cfg : EditorConfig) (km : Keymap) (s : EditorState) (key : Key) : StepResult :=
  let keys := s.pending ++ [key]
  match lookupKeys cfg km keys with
  | .command c => runCommand cfg c key { s with pending := [] }
  | .prefixOf => ok { s with pending := keys }
  | .unbound =>
    if !s.pending.isEmpty then bell { s with pending := [], arg := none }
    else match key.printable? with
      | some _ => runCommand cfg .selfInsert key s
      | none => bell { s with arg := none }

end Leanline.Editor
