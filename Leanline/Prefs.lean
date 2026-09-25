import Leanline.Key
import Leanline.KeyDecoder
import Leanline.History

/-!
# User preferences

Preferences belong to the user rather than the program, and are read from
`~/.leanline`. The format is Haskeline's: one `field: value` per line, field
names case-insensitive; `--` and `#` start comments. Values are accepted in
Haskeline's spelling (`Just 100`, `Vi`, `IgnoreConsecutive`, `True`) and in
plain form (`100`, `vi`, `ignore-consecutive`, `yes`).

```
editMode: Vi
bellStyle: NoBell
maxHistorySize: Just 1000
historyDuplicates: IgnoreConsecutive
completionType: MenuCompletion
bind: ctrl-t up
keyseq: xterm "\ESC[1;5D" ctrl-left
```

Unlike Haskeline, problems are not silently ignored: `Prefs.parse` returns a
list of diagnostics alongside the preferences.
-/

namespace Leanline

inductive EditMode where
  | emacs
  | vi
  deriving DecidableEq, Repr, Inhabited

inductive BellStyle where
  | none
  | visual
  | audible
  deriving DecidableEq, Repr, Inhabited

inductive CompletionType where
  /-- Insert the common prefix; list the candidates when ambiguous. -/
  | list
  /-- Cycle through the candidates on each Tab. -/
  | menu
  deriving DecidableEq, Repr, Inhabited

structure Prefs where
  editMode : EditMode := .emacs
  bellStyle : BellStyle := .audible
  maxHistorySize : Option Nat := some 100
  historyDuplicates : DuplicatePolicy := .alwaysAdd
  completionType : CompletionType := .list
  /-- Page long completion listings with a `--More--` prompt. -/
  completionPaging : Bool := true
  /-- Ask before listing more than this many candidates. -/
  completionPromptLimit : Option Nat := some 100
  /-- List candidates on the first ambiguous Tab rather than the second. -/
  listCompletionsImmediately : Bool := true
  /-- `bind:` lines: a key that acts as a sequence of other keys. -/
  customBindings : List (Key × List Key) := []
  /-- `keyseq:` lines: extra escape sequences, optionally for one `$TERM` only. -/
  customKeySequences : List (Option String × List UInt8 × Key) := []
  /-- Milliseconds to wait for the rest of an escape sequence. -/
  keySeqTimeout : Nat := 50
  /-- Show fish-style suggestions from history after the cursor. -/
  historySuggestions : Bool := false
  /-- Up/Down search history for entries starting with the text before the cursor. -/
  prefixHistorySearch : Bool := false
  /-- In vi mode, show the mode through the cursor shape (bar, block, underline). -/
  viCursorShape : Bool := true
  deriving Repr, Inhabited

namespace Prefs

def defaultPrefs : Prefs := {}

private def norm (s : String) : String :=
  String.ofList ((Text.lower s.toList).filter fun c => c != '-' && c != '_' && c != ' ')

private def trimStr (s : String) : String := Text.trimString s

def parseBool (s : String) : Option Bool :=
  match norm s with
  | "true" | "yes" | "on" | "1" => some true
  | "false" | "no" | "off" | "0" => some false
  | _ => none

def parseMaybeNat (s : String) : Option (Option Nat) :=
  let n := norm s
  if n == "nothing" || n == "none" || n == "unlimited" then some none
  else
    let body := if Text.isPrefix "just" n then n.toList.drop 4 else n.toList
    (Text.toNat? body).map some

def parseEditMode (s : String) : Option EditMode :=
  match norm s with
  | "vi" => some .vi
  | "emacs" => some .emacs
  | _ => none

def parseBellStyle (s : String) : Option BellStyle :=
  match norm s with
  | "nobell" | "none" | "off" => some .none
  | "visualbell" | "visual" => some .visual
  | "audiblebell" | "audible" | "on" => some .audible
  | _ => none

def parseDuplicates (s : String) : Option DuplicatePolicy :=
  match norm s with
  | "alwaysadd" | "always" => some .alwaysAdd
  | "ignoreconsecutive" | "consecutive" => some .ignoreConsecutive
  | "ignoreall" | "all" => some .ignoreAll
  | _ => none

def parseCompletionType (s : String) : Option CompletionType :=
  match norm s with
  | "listcompletion" | "list" => some .list
  | "menucompletion" | "menu" => some .menu
  | _ => none

/-- Decode a double-quoted string with Haskell-style escapes: `\ESC`, `\e`,
`\n`, `\t`, `\r`, `\\`, `\"`, decimal `\27` and hex `\x1b`. Returns the bytes
and the text after the closing quote. -/
def parseQuoted (s : String) : Option (List UInt8 × String) :=
  match s.toList with
  | '"' :: rest => go rest.length rest []
  | _ => none
where
  isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
  hexVal (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  utf8 (c : Char) : List UInt8 := String.utf8EncodeChar c
  -- Each step consumes at least one character, so the length is enough fuel.
  go : Nat → List Char → List UInt8 → Option (List UInt8 × String)
    | 0, _, _ => none
    | _, [], _ => none
    | _ + 1, '"' :: rest, acc => some (acc.reverse, String.ofList rest)
    | fuel + 1, '\\' :: 'E' :: 'S' :: 'C' :: rest, acc => go fuel rest (0x1B :: acc)
    | fuel + 1, '\\' :: 'e' :: rest, acc => go fuel rest (0x1B :: acc)
    | fuel + 1, '\\' :: 'n' :: rest, acc => go fuel rest (0x0A :: acc)
    | fuel + 1, '\\' :: 't' :: rest, acc => go fuel rest (0x09 :: acc)
    | fuel + 1, '\\' :: 'r' :: rest, acc => go fuel rest (0x0D :: acc)
    | fuel + 1, '\\' :: 'x' :: rest, acc =>
      let ds := rest.takeWhile (hexVal · |>.isSome)
      let v := ds.foldl (fun a d => a * 16 + (hexVal d).getD 0) 0
      go fuel (rest.drop ds.length) (v.toUInt8 :: acc)
    | fuel + 1, '\\' :: c :: rest, acc =>
      if isDigit c then
        let ds := (c :: rest).takeWhile isDigit
        let v := ds.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0
        go fuel ((c :: rest).drop ds.length) (v.toUInt8 :: acc)
      else go fuel rest ((utf8 c).reverse ++ acc)
    | fuel + 1, c :: rest, acc => go fuel rest ((utf8 c).reverse ++ acc)

/-- Apply one `field: value` setting. -/
def applySetting (p : Prefs) (field value : String) : Except String Prefs :=
  let bad := Except.error s!"invalid value for {field}: {value}"
  let orBad {α : Type} (o : Option α) (f : α → Prefs) : Except String Prefs :=
    match o with | some a => .ok (f a) | none => bad
  match norm field with
  | "editmode" => orBad (parseEditMode value) fun v => { p with editMode := v }
  | "bellstyle" => orBad (parseBellStyle value) fun v => { p with bellStyle := v }
  | "maxhistorysize" => orBad (parseMaybeNat value) fun v => { p with maxHistorySize := v }
  | "historyduplicates" => orBad (parseDuplicates value) fun v => { p with historyDuplicates := v }
  | "completiontype" => orBad (parseCompletionType value) fun v => { p with completionType := v }
  | "completionpaging" => orBad (parseBool value) fun v => { p with completionPaging := v }
  | "completionpromptlimit" => orBad (parseMaybeNat value) fun v => { p with completionPromptLimit := v }
  | "listcompletionsimmediately" => orBad (parseBool value) fun v => { p with listCompletionsImmediately := v }
  | "keyseqtimeout" => orBad (Text.toNat? value.toList) fun v => { p with keySeqTimeout := v }
  | "historysuggestions" => orBad (parseBool value) fun v => { p with historySuggestions := v }
  | "prefixhistorysearch" => orBad (parseBool value) fun v => { p with prefixHistorySearch := v }
  | "vicursorshape" => orBad (parseBool value) fun v => { p with viCursorShape := v }
  | "bind" =>
    match Key.parseSeq? value with
    | some (k :: ks) => .ok { p with customBindings := p.customBindings ++ [(k, ks)] }
    | _ => bad
  | "keyseq" =>
    let (term, rest) :=
      if Text.isPrefix "\"" value then (none, value)
      else match Text.splitFirst ' ' value.toList with
        | some (t, more) => (some (String.ofList t), trimStr (String.ofList more))
        | none => (none, value)
    match parseQuoted rest with
    | some (bytes, keyText) =>
      match Key.parse? (trimStr keyText) with
      | some k => if bytes.isEmpty then bad
                  else .ok { p with customKeySequences := p.customKeySequences ++ [(term, bytes, k)] }
      | none => bad
    | none => bad
  | _ => .error s!"unknown preference: {field}"

/-- Parse a preferences file. Returns the preferences and one diagnostic per
line that could not be understood (those lines are skipped). -/
def parse (contents : String) (base : Prefs := {}) : Prefs × List String :=
  let lines := Text.splitOn '\n' contents.toList
  lines.zipIdx.foldl (init := (base, [])) fun (p, errs) (line, i) =>
    let l := Text.trim line
    if l.isEmpty || "--".toList.isPrefixOf l || "#".toList.isPrefixOf l then (p, errs)
    else match Text.splitFirst ':' l with
      | none => (p, errs ++ [s!"line {i + 1}: expected 'field: value'"])
      | some (field, value) =>
        match applySetting p (String.ofList (Text.trim field)) (String.ofList (Text.trim value)) with
        | .ok p' => (p', errs)
        | .error e => (p, errs ++ [s!"line {i + 1}: {e}"])

/-- Default location of the preferences file: `~/.leanline`. -/
def defaultPath : IO (Option System.FilePath) := do
  return (← IO.getEnv "HOME").map fun home => (home : System.FilePath) / ".leanline"

/-- Read preferences from a file; a missing or unreadable file gives the defaults. -/
def readFile (path : System.FilePath) : IO Prefs := do
  try
    if !(← path.pathExists) then return {}
    return (parse (← IO.FS.readFile path)).1
  catch _ => return {}

/-- Key sequences that apply to the terminal named `term`. -/
def keySeqTable (p : Prefs) (term : Option String) : KeySeqTable :=
  p.customKeySequences.filterMap fun (t, bytes, k) =>
    if t.isNone || t == term then some (bytes, k) else none

end Prefs

end Leanline
