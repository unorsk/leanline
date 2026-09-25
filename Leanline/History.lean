import Leanline.Text

/-!
# History

`History` is an immutable value: a list of previously entered lines, newest
first, with an optional size bound. It is independent of any terminal and can
be loaded from and saved to a file.
-/

namespace Leanline

/-- What to do when a line equal to an existing history entry is added. -/
inductive DuplicatePolicy where
  /-- Always record the line. -/
  | alwaysAdd
  /-- Skip the line if it equals the most recent entry. -/
  | ignoreConsecutive
  /-- Remove every earlier occurrence of the line before recording it. -/
  | ignoreAll
  deriving DecidableEq, Repr, Inhabited

structure History where
  /-- Entries, newest first. -/
  entries : List String := []
  /-- Maximum number of entries kept, if bounded. -/
  maxSize : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

namespace History

def empty : History := {}

/-- Entries from newest to oldest. -/
def newestFirst (h : History) : List String := h.entries

/-- Entries from oldest to newest. -/
def oldestFirst (h : History) : List String := h.entries.reverse

def size (h : History) : Nat := h.entries.length

/-- Drop the oldest entries so that at most `maxSize` remain. -/
def enforceLimit (h : History) : History :=
  match h.maxSize with
  | some n => { h with entries := h.entries.take n }
  | none => h

/-- Bound the history to `n` entries (or unbound it), truncating if needed. -/
def stifle (n : Option Nat) (h : History) : History := enforceLimit { h with maxSize := n }

/-- The current bound, if any. -/
def stifleAmount (h : History) : Option Nat := h.maxSize

/-- Record a line unconditionally. -/
def add (line : String) (h : History) : History :=
  enforceLimit { h with entries := line :: h.entries }

/-- Record a line unless it equals the most recent entry. -/
def addUnlessConsecutiveDupe (line : String) (h : History) : History :=
  if h.entries.head? == some line then h else h.add line

/-- Record a line after removing all earlier occurrences of it. -/
def addRemovingAllDupes (line : String) (h : History) : History :=
  enforceLimit { h with entries := line :: h.entries.filter (· != line) }

def addWith (policy : DuplicatePolicy) (line : String) (h : History) : History :=
  match policy with
  | .alwaysAdd => h.add line
  | .ignoreConsecutive => h.addUnlessConsecutiveDupe line
  | .ignoreAll => h.addRemovingAllDupes line

/-! ## File format

One entry per line, oldest first, UTF-8. Backslashes and newlines inside an
entry are escaped as `\\` and `\n`, so multi-line entries survive a round
trip. Any other backslash sequence is read literally, which keeps plain
history files written by other tools (for example Haskeline's) readable. -/

def escapeChar (c : Char) : List Char :=
  if c == '\\' then ['\\', '\\']
  else if c == '\n' then ['\\', 'n']
  else if c == '\r' then ['\\', 'r']
  else [c]

def escapeChars : List Char → List Char
  | [] => []
  | c :: cs => escapeChar c ++ escapeChars cs

def escapeEntry (s : String) : String := String.ofList (escapeChars s.toList)

/-- The character that `\c` stands for. -/
def unescapeOne : Char → Option Char
  | '\\' => some '\\'
  | 'n' => some '\n'
  | 'r' => some '\r'
  | _ => none

/-- Decode escapes; `pending` means a backslash has just been read. -/
def unescapeAux : Bool → List Char → List Char
  | pending, [] => if pending then ['\\'] else []
  | false, c :: cs => if c == '\\' then unescapeAux true cs else c :: unescapeAux false cs
  | true, c :: cs =>
    match unescapeOne c with
    | some e => e :: unescapeAux false cs
    | none => '\\' :: c :: unescapeAux false cs

def unescapeChars (cs : List Char) : List Char := unescapeAux false cs

def unescapeEntry (s : String) : String := String.ofList (unescapeChars s.toList)

/-- Serialise to the file format. -/
def serialize (h : History) : String :=
  String.join (h.oldestFirst.map fun e => escapeEntry e ++ "\n")

/-- Parse the file format. Blank lines are ignored. -/
def parse (contents : String) (maxSize : Option Nat := none) : History :=
  let lines := (Text.splitOn '\n' contents.toList).map fun l =>
    if l.getLast? == some '\r' then l.dropLast else l
  let entries := (lines.filter (!·.isEmpty)).map fun l => String.ofList (unescapeChars l)
  enforceLimit { entries := entries.reverse, maxSize }

/-- Load a history file. A missing file yields an empty history. -/
def readFile (path : System.FilePath) (maxSize : Option Nat := none) : IO History := do
  if !(← path.pathExists) then return { maxSize }
  let bytes ← IO.FS.readBinFile path
  let contents := (String.fromUTF8? bytes).getD (String.ofList (bytes.toList.map (Char.ofNat ·.toNat)))
  return parse contents maxSize

/-- Save a history file atomically (write to a temporary file, then rename). -/
def writeFile (path : System.FilePath) (h : History) : IO Unit := do
  if let some dir := path.parent then
    if dir.toString != "" then IO.FS.createDirAll dir
  let tmp : System.FilePath := path.toString ++ ".tmp"
  IO.FS.writeFile tmp h.serialize
  IO.FS.rename tmp path

end History

/-!
# History navigation

While a line is being edited the history is viewed through a zipper: the
entries older than the one shown, and the ones newer than it. The shown line
itself lives in the editor's buffer, so edits made to a recalled entry are kept
while navigating (as in Haskeline and readline) without touching the stored
history.
-/

structure HistoryNav where
  /-- Entries older than the displayed one, nearest first. -/
  older : List String := []
  /-- Entries newer than the displayed one, nearest first. -/
  newer : List String := []
  deriving DecidableEq, Repr, Inhabited

namespace HistoryNav

def ofHistory (h : History) : HistoryNav := { older := h.entries }

/-- Step to the next older entry, stashing the current line. -/
def back (current : String) (n : HistoryNav) : Option (String × HistoryNav) :=
  match n.older with
  | e :: rest => some (e, { older := rest, newer := current :: n.newer })
  | [] => none

/-- Step to the next newer entry, stashing the current line. -/
def forward (current : String) (n : HistoryNav) : Option (String × HistoryNav) :=
  match n.newer with
  | e :: rest => some (e, { older := current :: n.older, newer := rest })
  | [] => none

/-- Index of the displayed entry counted from the newest end (0 = the line being typed). -/
def depth (n : HistoryNav) : Nat := n.newer.length

/-- Step back repeatedly until an entry satisfies `p`. -/
def backUntil (p : String → Bool) (current : String) (n : HistoryNav) : Option (String × HistoryNav) :=
  go current n.newer n.older
where
  go (cur : String) (newer : List String) : List String → Option (String × HistoryNav)
    | [] => none
    | e :: rest => if p e then some (e, { older := rest, newer := cur :: newer }) else go e (cur :: newer) rest

/-- Step forward repeatedly until an entry satisfies `p`. -/
def forwardUntil (p : String → Bool) (current : String) (n : HistoryNav) : Option (String × HistoryNav) :=
  go current n.older n.newer
where
  go (cur : String) (older : List String) : List String → Option (String × HistoryNav)
    | [] => none
    | e :: rest => if p e then some (e, { older := cur :: older, newer := rest }) else go e (cur :: older) rest

/-- Jump to the oldest entry. -/
def toOldest (current : String) (n : HistoryNav) : String × HistoryNav :=
  match n.older.reverse with
  | [] => (current, n)
  | oldest :: _ =>
    let all := n.older.reverse ++ [current] ++ n.newer
    (oldest, { older := [], newer := all.tail })

/-- Jump back to the line being typed. -/
def toNewest (current : String) (n : HistoryNav) : String × HistoryNav :=
  match n.newer.reverse with
  | [] => (current, n)
  | newest :: _ =>
    let all := n.newer.reverse ++ [current] ++ n.older
    (newest, { older := all.tail, newer := [] })

end HistoryNav

end Leanline
