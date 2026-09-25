import Leanline.Unicode

/-!
# Graphemes

The editor moves the cursor over user-perceived characters, not code points:
a base character together with the combining marks, joiners and modifiers
that follow it. This is a pragmatic subset of UAX #29 that handles combining
diacritics, emoji ZWJ sequences, skin-tone modifiers and flag pairs.
-/

namespace Leanline

structure Grapheme where
  base : Char
  marks : List Char := []
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Grapheme

def ofChar (c : Char) : Grapheme := ⟨c, []⟩

instance : Coe Char Grapheme := ⟨ofChar⟩

def toList (g : Grapheme) : List Char := g.base :: g.marks

protected def toString (g : Grapheme) : String := String.ofList g.toList

instance : ToString Grapheme := ⟨Grapheme.toString⟩

/-- Does `c` continue the grapheme `g` rather than start a new one? -/
def joins (g : Grapheme) (c : Char) : Bool :=
  Unicode.isCombining c ||
  g.marks.getLast? == some Unicode.zeroWidthJoiner ||
  (Unicode.isRegionalIndicator c && Unicode.isRegionalIndicator g.base && g.marks.isEmpty)

/-- Terminal cells occupied by the grapheme (0 for control characters). -/
def width (g : Grapheme) : Nat :=
  if Unicode.isRegionalIndicator g.base && !g.marks.isEmpty then 2
  else if g.marks.contains '️' && Unicode.charWidth g.base == 1 && g.base.toNat ≥ 0x2000 then 2
  else Unicode.charWidth g.base

def isWord (g : Grapheme) : Bool := Unicode.isWordChar g.base
def isSpace (g : Grapheme) : Bool := Unicode.isSpace g.base

def map (f : Char → Char) (g : Grapheme) : Grapheme := { g with base := f g.base }
def toUpper (g : Grapheme) : Grapheme := g.map Unicode.toUpper
def toLower (g : Grapheme) : Grapheme := g.map Unicode.toLower
def toggleCase (g : Grapheme) : Grapheme :=
  if Unicode.isUpper g.base then g.toLower else g.toUpper

end Grapheme

/-- Add one character to a reversed grapheme list (head = last grapheme). -/
def pushChar : List Grapheme → Char → List Grapheme
  | g :: rest, c => if g.joins c then { g with marks := g.marks ++ [c] } :: rest else ⟨c, []⟩ :: g :: rest
  | [], c => [⟨c, []⟩]

/-- Segment characters into graphemes. -/
def graphemes (cs : List Char) : List Grapheme := (cs.foldl pushChar []).reverse

def graphemesOf (s : String) : List Grapheme := graphemes s.toList

/-- Flatten graphemes back to characters. -/
def charsOf (gs : List Grapheme) : List Char := gs.flatMap Grapheme.toList

def stringOf (gs : List Grapheme) : String := String.ofList (charsOf gs)

def widthOf (gs : List Grapheme) : Nat := gs.foldl (fun n g => n + g.width) 0

end Leanline
