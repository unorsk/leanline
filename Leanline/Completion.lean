/-!
# Completion

A completion function receives the text on both sides of the cursor and
answers with the part of the left text to keep plus the candidates that may
follow it. Combinators build completion functions for words, quoted words and
file names.
-/

namespace Leanline

structure Completion where
  /-- Text inserted in place of the word being completed. -/
  replacement : String
  /-- Text shown when listing candidates. -/
  display : String := replacement
  /-- Whether the word is complete; if so a space is inserted after it. -/
  isFinished : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- The line around the cursor. -/
structure CompletionRequest where
  before : String
  after : String
  deriving DecidableEq, Repr, Inhabited

structure CompletionResult where
  /-- The text left of the cursor that is kept; candidates are inserted after it. -/
  kept : String
  candidates : List Completion
  deriving DecidableEq, Repr, Inhabited

abbrev CompletionFunc (m : Type → Type) := CompletionRequest → m CompletionResult

def simpleCompletion (s : String) : Completion := { replacement := s }

/-- A completion function that never proposes anything. -/
def noCompletion {m : Type → Type} [Monad m] : CompletionFunc m :=
  fun req => pure { kept := req.before, candidates := [] }

/-- Try `first`; if it has no candidates use `second`. -/
def fallbackCompletion {m : Type → Type} [Monad m] (first second : CompletionFunc m) : CompletionFunc m :=
  fun req => do
    let r ← first req
    if r.candidates.isEmpty then second req else pure r

/-! ## Pure helpers -/

def commonPrefix : List Char → List Char → List Char
  | a :: as, b :: bs => if a == b then a :: commonPrefix as bs else []
  | _, _ => []

def longestCommonPrefix : List (List Char) → List Char
  | [] => []
  | x :: xs => xs.foldl commonPrefix x

/-- Index at which the word ending at the cursor starts: just after the last
break character that is not preceded by the escape character. -/
def wordStart (escape : Option Char) (isBreak : Char → Bool) : List Char → Nat → Nat → Nat
  | [], _, start => start
  | c :: rest, i, start =>
    if escape == some c then
      match rest with
      | _ :: rest' => wordStart escape isBreak rest' (i + 2) start
      | [] => start
    else if isBreak c then wordStart escape isBreak rest (i + 1) (i + 1)
    else wordStart escape isBreak rest (i + 1) start

/-- Remove escape characters (each escapes the character after it). -/
def unescapeWith (escape : Option Char) : List Char → List Char
  | c :: d :: rest => if escape == some c then d :: unescapeWith escape rest else c :: unescapeWith escape (d :: rest)
  | cs => cs

/-- Escape every character satisfying `needs` (and the escape character itself). -/
def escapeWith (escape : Option Char) (needs : Char → Bool) (cs : List Char) : List Char :=
  match escape with
  | none => cs
  | some e => cs.flatMap fun c => if c == e || needs c then [e, c] else [c]

private def escapeCompletion (escape : Option Char) (needs : Char → Bool) (c : Completion) : Completion :=
  { c with replacement := String.ofList (escapeWith escape needs c.replacement.toList) }

/-- Split the text left of the cursor into the kept prefix and the (unescaped) word. -/
def splitWord (escape : Option Char) (breakChars : List Char) (before : String) : String × String :=
  let cs := before.toList
  let s := wordStart escape (breakChars.contains ·) cs 0 0
  (String.ofList (cs.take s), String.ofList (unescapeWith escape (cs.drop s)))

/-! ## Combinators -/

/-- Complete the word immediately left of the cursor. A word begins at the
start of the line or after an unescaped break character. The word is passed
unescaped; candidate replacements are escaped automatically. -/
def completeWord {m : Type → Type} [Monad m] (escape : Option Char) (breakChars : List Char)
    (f : String → m (List Completion)) : CompletionFunc m := fun req => do
  let (kept, word) := splitWord escape breakChars req.before
  let cands ← f word
  return { kept, candidates := cands.map (escapeCompletion escape (breakChars.contains ·)) }

/-- Like `completeWord`, but `f` also receives the text before the word. -/
def completeWordWithPrev {m : Type → Type} [Monad m] (escape : Option Char) (breakChars : List Char)
    (f : String → String → m (List Completion)) : CompletionFunc m := fun req => do
  let (kept, word) := splitWord escape breakChars req.before
  let cands ← f kept word
  return { kept, candidates := cands.map (escapeCompletion escape (breakChars.contains ·)) }

/-- Complete from a fixed list of words. -/
def completeFromList {m : Type → Type} [Monad m] (words : List String)
    (breakChars : List Char := [' ', '\t']) : CompletionFunc m :=
  completeWord none breakChars fun w =>
    pure ((words.filter (w.isPrefixOf ·)).map simpleCompletion)

/-- If the cursor is inside an unclosed quote, returns the index of the
opening quote and the quote character. -/
def openQuote (escape : Option Char) (quotes : List Char) : List Char → Nat → Option (Nat × Char) → Option (Nat × Char)
  | [], _, st => st
  | c :: rest, i, st =>
    if escape == some c then
      match rest with
      | _ :: rest' => openQuote escape quotes rest' (i + 2) st
      | [] => st
    else match st with
      | some (_, q) => if c == q then openQuote escape quotes rest (i + 1) none
                       else openQuote escape quotes rest (i + 1) st
      | none => if quotes.contains c then openQuote escape quotes rest (i + 1) (some (i, c))
                else openQuote escape quotes rest (i + 1) none

/-- Complete inside quotes with `f` (closing the quote on finished
candidates); outside quotes defer to `alternative`. -/
def completeQuotedWord {m : Type → Type} [Monad m] (escape : Option Char) (quotes : List Char)
    (f : String → m (List Completion)) (alternative : CompletionFunc m) : CompletionFunc m := fun req => do
  let cs := req.before.toList
  match openQuote escape quotes cs 0 none with
  | none => alternative req
  | some (i, q) =>
    let word := unescapeWith escape (cs.drop (i + 1))
    let cands ← f (String.ofList word)
    let fix (c : Completion) : Completion :=
      let r := String.ofList (escapeWith escape (· == q) c.replacement.toList)
      { c with replacement := if c.isFinished then r.push q else r }
    return { kept := String.ofList (cs.take (i + 1)), candidates := cands.map fix }

/-! ## File names -/

/-- Characters that end a file name word in `completeFilename`. -/
def filenameWordBreakChars : List Char := " \t\n`@$><=;|&{(".toList

/-- Expand a leading `~` or `~/` using `$HOME`. -/
def expandTilde (path : String) : IO String := do
  if path == "~" || path.startsWith "~/" then
    match ← IO.getEnv "HOME" with
    | some home => return home ++ String.ofList (path.toList.drop 1)
    | none => return path
  else return path

/-- File-system candidates for a partial path. Directories are unfinished and
end in `/`, so completion can continue into them. -/
def listFilesIO (path : String) : IO (List Completion) := do
  let cs := path.toList
  let slash := cs.length - ((cs.reverse.takeWhile (· != '/')).length)
  let dirPart := String.ofList (cs.take slash)
  let filePart := String.ofList (cs.drop slash)
  let dir ← expandTilde (if dirPart.isEmpty then "." else dirPart)
  let entries ← try System.FilePath.readDir dir catch _ => pure #[]
  let showHidden := filePart.startsWith "."
  let mut out : Array Completion := #[]
  for e in entries do
    let name := e.fileName
    if filePart.isPrefixOf name && (showHidden || !name.startsWith ".") && name != "." && name != ".." then
      let isDir ← (dir ++ "/" ++ name : System.FilePath).isDir
      let suffix := if isDir then "/" else ""
      out := out.push { replacement := dirPart ++ name ++ suffix, display := name ++ suffix, isFinished := !isDir }
  return (out.qsort (fun a b => a.replacement < b.replacement)).toList

def listFiles {m : Type → Type} [MonadLiftT IO m] (path : String) : m (List Completion) :=
  monadLift (listFilesIO path)

/-- File name completion with backslash escapes and single or double quotes. -/
def completeFilename {m : Type → Type} [Monad m] [MonadLiftT IO m] : CompletionFunc m :=
  completeQuotedWord (some '\\') ['"', '\''] listFiles <|
    completeWord (some '\\') (['"', '\''] ++ filenameWordBreakChars) listFiles

end Leanline
