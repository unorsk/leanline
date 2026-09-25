import Leanline.Grapheme

/-!
# Line buffer

A zipper over graphemes. `before` holds the graphemes left of the cursor in
reverse order (its head is adjacent to the cursor) and `after` holds the
graphemes from the cursor to the end of the line. Every value of this type
is a valid buffer with a valid cursor, so no operation can go out of bounds,
and every operation below is total.
-/

namespace Leanline

structure LineBuffer where
  before : List Grapheme := []
  after : List Grapheme := []
  deriving DecidableEq, Repr, Inhabited

namespace LineBuffer

def empty : LineBuffer := {}

/-- All graphemes in order. -/
def graphemes (b : LineBuffer) : List Grapheme := b.before.reverse ++ b.after

def chars (b : LineBuffer) : List Char := charsOf b.graphemes

protected def toString (b : LineBuffer) : String := String.ofList b.chars

instance : ToString LineBuffer := ⟨LineBuffer.toString⟩

/-- Cursor position, counted in graphemes from the start of the line. -/
def pos (b : LineBuffer) : Nat := b.before.length

def length (b : LineBuffer) : Nat := b.before.length + b.after.length

def isEmpty (b : LineBuffer) : Bool := b.before.isEmpty && b.after.isEmpty

def atStart (b : LineBuffer) : Bool := b.before.isEmpty
def atEnd (b : LineBuffer) : Bool := b.after.isEmpty

def textBefore (b : LineBuffer) : String := stringOf b.before.reverse
def textAfter (b : LineBuffer) : String := stringOf b.after

/-- Build a buffer from graphemes with the cursor after `l`. -/
def ofLists (l r : List Grapheme) : LineBuffer := ⟨l.reverse, r⟩

/-- A buffer holding `s` with the cursor at the end. -/
def ofString (s : String) : LineBuffer := ofLists (graphemesOf s) []

/-- A buffer holding `l ++ r` with the cursor between them. -/
def ofParts (l r : String) : LineBuffer := ofLists (graphemesOf l) (graphemesOf r)

/-! ## Insertion and deletion -/

def insert (g : Grapheme) (b : LineBuffer) : LineBuffer := { b with before := g :: b.before }

def insertList (gs : List Grapheme) (b : LineBuffer) : LineBuffer :=
  { b with before := gs.reverse ++ b.before }

/-- Insert a typed character. A combining mark attaches to the grapheme on the
left of the cursor instead of forming a grapheme of its own. -/
def insertChar (c : Char) (b : LineBuffer) : LineBuffer :=
  match b.before with
  | g :: rest => if g.joins c then { b with before := { g with marks := g.marks ++ [c] } :: rest }
                 else b.insert (Grapheme.ofChar c)
  | [] => b.insert (Grapheme.ofChar c)

def insertString (s : String) (b : LineBuffer) : LineBuffer :=
  s.toList.foldl (fun acc c => acc.insertChar c) b

/-- Insert text to the right of the cursor, leaving the cursor where it is. -/
def insertListAfter (gs : List Grapheme) (b : LineBuffer) : LineBuffer :=
  { b with after := gs ++ b.after }

def deleteBackward (b : LineBuffer) : LineBuffer := { b with before := b.before.tail }
def deleteForward (b : LineBuffer) : LineBuffer := { b with after := b.after.tail }

/-- Replace the grapheme under the cursor (no-op at the end of the line). -/
def replaceCurrent (g : Grapheme) (b : LineBuffer) : LineBuffer :=
  match b.after with
  | _ :: r => { b with after := g :: r }
  | [] => b

/-! ## Movement -/

def moveLeft (b : LineBuffer) : LineBuffer :=
  match b.before with
  | g :: l => ⟨l, g :: b.after⟩
  | [] => b

def moveRight (b : LineBuffer) : LineBuffer :=
  match b.after with
  | g :: r => ⟨g :: b.before, r⟩
  | [] => b

def moveToStart (b : LineBuffer) : LineBuffer := ⟨[], b.before.reverse ++ b.after⟩

def moveToEnd (b : LineBuffer) : LineBuffer := ⟨b.after.reverse ++ b.before, []⟩

/-- Put the cursor at grapheme index `n` (clamped to the line length). -/
def moveTo (n : Nat) (b : LineBuffer) : LineBuffer :=
  let gs := b.graphemes
  ⟨(gs.take n).reverse, gs.drop n⟩

def iterate (n : Nat) (f : LineBuffer → LineBuffer) (b : LineBuffer) : LineBuffer :=
  match n with
  | 0 => b
  | n + 1 => iterate n f (f b)

/-- Move graphemes from `l` to `r` while `p` holds for the head of `l`. -/
def spanLeft (p : Grapheme → Bool) : List Grapheme → List Grapheme → List Grapheme × List Grapheme
  | g :: l, r => if p g then spanLeft p l (g :: r) else (g :: l, r)
  | [], r => ([], r)

/-- Move graphemes from `r` to `l` while `p` holds for the head of `r`. -/
def spanRight (p : Grapheme → Bool) : List Grapheme → List Grapheme → List Grapheme × List Grapheme
  | l, g :: r => if p g then spanRight p (g :: l) r else (l, g :: r)
  | l, [] => (l, [])

/-- Move left while the grapheme left of the cursor satisfies `p`. -/
def skipLeft (p : Grapheme → Bool) (b : LineBuffer) : LineBuffer :=
  let (l, r) := spanLeft p b.before b.after
  ⟨l, r⟩

/-- Move right while the grapheme under the cursor satisfies `p`. -/
def skipRight (p : Grapheme → Bool) (b : LineBuffer) : LineBuffer :=
  let (l, r) := spanRight p b.before b.after
  ⟨l, r⟩

/-- Emacs `backward-word`: skip non-word characters, then word characters. -/
def wordLeft (b : LineBuffer) : LineBuffer :=
  (b.skipLeft (fun g => !g.isWord)).skipLeft Grapheme.isWord

/-- Emacs `forward-word`: skip non-word characters, then word characters. -/
def wordRight (b : LineBuffer) : LineBuffer :=
  (b.skipRight (fun g => !g.isWord)).skipRight Grapheme.isWord

/-- Whitespace-delimited word to the left (`unix-word-rubout`). -/
def bigWordLeft (b : LineBuffer) : LineBuffer :=
  (b.skipLeft Grapheme.isSpace).skipLeft (fun g => !g.isSpace)

def bigWordRight (b : LineBuffer) : LineBuffer :=
  (b.skipRight Grapheme.isSpace).skipRight (fun g => !g.isSpace)

/-- Character class used by vi word motions: blank, word, or punctuation. -/
def charClass (g : Grapheme) : Nat :=
  if g.isSpace then 0 else if g.isWord then 1 else 2

/-- Class of a grapheme for vi big-word motions: blank or non-blank. -/
def bigClass (g : Grapheme) : Nat := if g.isSpace then 0 else 1

/-- vi `w` / `W`: to the start of the next word. -/
def viWordForward (cls : Grapheme → Nat) (b : LineBuffer) : LineBuffer :=
  match b.after with
  | [] => b
  | g :: _ =>
    let b := if cls g == 0 then b else b.skipRight (fun h => cls h == cls g)
    b.skipRight (fun h => cls h == 0)

/-- vi `b` / `B`: to the start of the previous word. -/
def viWordBackward (cls : Grapheme → Nat) (b : LineBuffer) : LineBuffer :=
  let b := b.skipLeft (fun h => cls h == 0)
  match b.before with
  | [] => b
  | g :: _ => b.skipLeft (fun h => cls h == cls g)

/-- vi `e` / `E`: to the end of the current or next word (on its last grapheme). -/
def viWordEnd (cls : Grapheme → Nat) (b : LineBuffer) : LineBuffer :=
  let b1 := b.moveRight.skipRight (fun h => cls h == 0)
  match b1.after with
  | [] => b1.moveLeft
  | g :: _ => (b1.skipRight (fun h => cls h == cls g)).moveLeft

/-- vi `^`: first non-blank character. -/
def firstNonBlank (b : LineBuffer) : LineBuffer := b.moveToStart.skipRight Grapheme.isSpace

/-- In vi command mode the cursor sits on a grapheme, never past the end. -/
def viClamp (b : LineBuffer) : LineBuffer :=
  match b.after, b.before with
  | [], _ :: _ => b.moveLeft
  | _, _ => b

/-- Find the `n`-th occurrence of `c` to the right of the cursor (exclusive). -/
def findForward (c : Grapheme) (n : Nat) (b : LineBuffer) : Option Nat :=
  let idxs := (b.after.zipIdx).filterMap fun (g, i) => if g == c && i > 0 then some i else none
  idxs[n - 1]? |>.map (b.pos + ·)

/-- Find the `n`-th occurrence of `c` to the left of the cursor. -/
def findBackward (c : Grapheme) (n : Nat) (b : LineBuffer) : Option Nat :=
  let idxs := (b.before.zipIdx).filterMap fun (g, i) => if g == c then some i else none
  idxs[n - 1]? |>.map (b.pos - 1 - ·)

/-! ## Multi-line buffers

A buffer may contain line breaks (multi-line input). These move between its
logical lines, keeping the column where possible. -/

def isNewline (g : Grapheme) : Bool := g.base == '\n'

/-- Column of the cursor within its logical line. -/
def column (b : LineBuffer) : Nat := (b.before.takeWhile (fun g => !isNewline g)).length

/-- Move to the previous logical line, or `none` on the first one. -/
def lineUp? (b : LineBuffer) : Option LineBuffer :=
  let col := b.column
  match b.before.drop col with
  | [] => none
  | _ :: prevRev =>
    let prevLen := (prevRev.takeWhile (fun g => !isNewline g)).length
    some (b.moveTo (b.pos - col - 1 - prevLen + min col prevLen))

/-- Move to the next logical line, or `none` on the last one. -/
def lineDown? (b : LineBuffer) : Option LineBuffer :=
  let col := b.column
  let restOfLine := (b.after.takeWhile (fun g => !isNewline g)).length
  match b.after.drop restOfLine with
  | [] => none
  | _ :: next =>
    let nextLen := (next.takeWhile (fun g => !isNewline g)).length
    some (b.moveTo (b.pos + restOfLine + 1 + min col nextLen))

/-! ## Region operations -/

/-- Delete the graphemes between the cursor and position `p`. Returns the new
buffer (cursor at the start of the deleted region) and the deleted text. -/
def deleteTo (p : Nat) (b : LineBuffer) : LineBuffer × List Grapheme :=
  let gs := b.graphemes
  let lo := min b.pos p
  let hi := max b.pos p
  (⟨(gs.take lo).reverse, gs.drop hi⟩, (gs.drop lo).take (hi - lo))

/-- Copy the graphemes between the cursor and position `p`. -/
def regionTo (p : Nat) (b : LineBuffer) : List Grapheme := (b.deleteTo p).2

/-- Kill with a motion: delete from the cursor to wherever `motion` would move it. -/
def deleteMotion (motion : LineBuffer → LineBuffer) (b : LineBuffer) : LineBuffer × List Grapheme :=
  b.deleteTo (motion b).pos

/-! ## Transformations -/

/-- Emacs `transpose-chars`. At the end of the line swaps the last two
graphemes; elsewhere swaps the graphemes around the cursor and advances. -/
def transpose (b : LineBuffer) : LineBuffer :=
  match b.before, b.after with
  | a :: c :: l, [] => ⟨c :: a :: l, []⟩
  | a :: l, c :: r => ⟨a :: c :: l, r⟩
  | _, _ => b

/-- Apply `f` to the next word (skipping leading non-word graphemes); the
function receives the index of each grapheme within the word. The cursor ends
after the word. -/
def mapWordForward (f : Nat → Grapheme → Grapheme) (b : LineBuffer) : LineBuffer :=
  let (pre, rest) := b.after.span (fun g => !g.isWord)
  let (word, rest) := rest.span Grapheme.isWord
  let word := word.zipIdx.map fun (g, i) => f i g
  ⟨(pre ++ word).reverse ++ b.before, rest⟩

def upcaseWord (b : LineBuffer) : LineBuffer := b.mapWordForward fun _ g => g.toUpper
def downcaseWord (b : LineBuffer) : LineBuffer := b.mapWordForward fun _ g => g.toLower
def capitalizeWord (b : LineBuffer) : LineBuffer :=
  b.mapWordForward fun i g => if i == 0 then g.toUpper else g.toLower

/-- vi `~`: toggle the case of `n` graphemes and move past them. -/
def toggleCaseForward (n : Nat) (b : LineBuffer) : LineBuffer :=
  let (xs, rest) := (b.after.take n, b.after.drop n)
  ⟨(xs.map Grapheme.toggleCase).reverse ++ b.before, rest⟩

/-- vi `r`: replace `n` graphemes starting at the cursor with `g`. Does nothing
if fewer than `n` graphemes remain. Leaves the cursor on the last replaced one. -/
def replaceChars (n : Nat) (g : Grapheme) (b : LineBuffer) : LineBuffer :=
  if n == 0 || b.after.length < n then b
  else (⟨(List.replicate n g) ++ b.before, b.after.drop n⟩ : LineBuffer).moveLeft

end LineBuffer

end Leanline
