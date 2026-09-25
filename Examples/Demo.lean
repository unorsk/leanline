import Leanline

/-!
# Leanline demo

A small REPL showing the main features:

* line editing with Emacs or vi keys (`~/.leanline`: `editMode: Vi`),
* persistent history (`.leanline-demo-history`), `C-r` search, `M-p` prefix search,
* completion of commands, then of file names,
* multi-line input: a line with unbalanced parentheses continues on Enter,
* syntax highlighting of the line as it is typed,
* passwords, single-key questions, custom key bindings,
* printing from another thread while the user is typing,
* Ctrl-C handling with `withInterrupt` / `handleInterrupt`.

Run it with `lake exe leanline-demo`.
-/

open Leanline

def commands : List String :=
  ["help", "history", "password", "confirm", "tick", "count", "clear-history", "quit"]

/-- Commands at the start of the line, file names elsewhere. -/
def completer : CompletionFunc IO :=
  completeWordWithPrev none [' '] (fun before word =>
    if before.trimAscii.isEmpty then
      pure ((commands.filter (word.isPrefixOf ·)).map simpleCompletion)
    else listFiles word)

/-- Syntax highlighting: known commands in bold green, numbers in cyan. -/
def highlight (line : String) : List Render.Span := Id.run do
  let mut spans := #[]
  let mut start := 0
  for w in line.splitOn " " do
    let stop := start + w.length
    if commands.contains w then
      spans := spans.push { start, stop, style := { fg := some .green, bold := true } }
    else if !w.isEmpty && w.all Char.isDigit then
      spans := spans.push { start, stop, style := { fg := some .cyan } }
    start := stop + 1
  return spans.toList

/-- Parentheses must balance before Enter accepts the input. -/
def balanced (s : String) : Bool :=
  s.toList.foldl (fun (depth : Int) c => if c == '(' then depth + 1 else if c == ')' then depth - 1 else depth) 0 ≤ 0

def settings : Settings IO :=
  { complete := completer
    historyFile := some ".leanline-demo-history"
    isComplete := balanced
    highlighter := some highlight
    -- Program-defined binding: C-o inserts a timestamp-like marker.
    keyBindings := [([Key.ctrl 'o'], .insertText "<now>")] }

/-- A long computation that can be interrupted with Ctrl-C. -/
def count (n : Nat) : InputT IO Unit := do
  for i in [0:n] do
    checkInterrupt
    if i % 10 == 0 then outputStrLn s!"  {i}"
    IO.sleep 100

partial def loop : InputT IO Unit := do
  let input ← getInputLine "\x1b[1;32mλ\x1b[0m "
  match input with
  | none => outputStrLn "Goodbye."
  | some line =>
    match line.trimAscii.toString with
    | "" => loop
    | "quit" => outputStrLn "Goodbye."
    | "help" =>
      outputStrLn s!"commands: {", ".intercalate commands}"
      loop
    | "history" =>
      let h ← getHistory
      for (entry, i) in h.oldestFirst.zipIdx do
        outputStrLn s!"{i + 1}  {entry}"
      loop
    | "clear-history" =>
      putHistory {}
      loop
    | "password" =>
      match ← getPassword (some '*') "password: " with
      | some p => outputStrLn s!"read {p.length} characters"
      | none => outputStrLn "cancelled"
      loop
    | "confirm" =>
      match ← getInputChar "Really? [y/n] " with
      | some 'y' => outputStrLn "Confirmed."
      | _ => outputStrLn "Not confirmed."
      loop
    | "tick" =>
      -- Another thread prints while the prompt is active.
      let print ← getExternalPrint
      let _ ← IO.asTask do
        for i in [1:4] do
          IO.sleep 1000
          print s!"[tick {i}]"
      loop
    | "count" =>
      handleInterrupt (outputStrLn "Interrupted.") (withInterrupt (count 100))
      loop
    | other =>
      outputStrLn s!"You typed: {other}"
      loop

def main : IO Unit := runInputT settings do
  if ← haveTerminalUI then
    outputStrLn "Leanline demo. Type 'help' for commands, Ctrl-D to exit."
  loop
