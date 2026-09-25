import Leanline.Unicode

/-!
# Text utilities

Small string helpers defined by structural recursion on character lists.
Unlike their `String` counterparts they reduce in the kernel, so everything
built on them (preference and history parsing, key names, completion) can be
checked by `decide` in the test theorems.
-/

namespace Leanline.Text

/-- Is `p` a prefix of `s`? -/
def isPrefix (p s : String) : Bool := p.toList.isPrefixOf s.toList

/-- Is `p` a suffix of `s`? -/
def isSuffix (p s : String) : Bool := p.toList.reverse.isPrefixOf s.toList.reverse

/-- Split at every occurrence of `sep`. -/
def splitOn (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c == sep then [] :: splitOn sep cs
    else match splitOn sep cs with
      | l :: ls => (c :: l) :: ls
      | [] => [[c]]

/-- Split at the first occurrence of `sep`. -/
def splitFirst (sep : Char) (cs : List Char) : Option (List Char × List Char) :=
  match cs.span (· != sep) with
  | (_, []) => none
  | (pre, _ :: post) => some (pre, post)

/-- Remove leading and trailing whitespace. -/
def trim (cs : List Char) : List Char :=
  ((cs.dropWhile Unicode.isSpace).reverse.dropWhile Unicode.isSpace).reverse

def trimString (s : String) : String := String.ofList (trim s.toList)

/-- Whitespace-separated words. -/
def words (cs : List Char) : List (List Char) :=
  (splitOn ' ' (cs.map fun c => if Unicode.isSpace c then ' ' else c)).filter (!·.isEmpty)

def wordsOf (s : String) : List String := (words s.toList).map String.ofList

/-- A non-empty string of ASCII digits. -/
def toNat? (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

def lower (cs : List Char) : List Char := cs.map Char.toLower

end Leanline.Text
