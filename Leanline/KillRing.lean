import Leanline.Grapheme

/-!
# Kill ring

Killed text is stored newest first. Consecutive kills are merged into one
entry (forward kills append, backward kills prepend), as in Emacs.
-/

namespace Leanline

structure KillRing where
  entries : List (List Grapheme) := []
  capacity : Nat := 60
  deriving DecidableEq, Repr, Inhabited

namespace KillRing

def top? (k : KillRing) : Option (List Grapheme) := k.entries.head?

/-- Add a new entry. Empty kills are not recorded. -/
def push (text : List Grapheme) (k : KillRing) : KillRing :=
  if text.isEmpty then k
  else { k with entries := (text :: k.entries).take k.capacity }

/-- Extend the newest entry: `prepend` for backward kills, append otherwise. -/
def merge (text : List Grapheme) (prepend : Bool) (k : KillRing) : KillRing :=
  match k.entries with
  | e :: rest => { k with entries := (if prepend then text ++ e else e ++ text) :: rest }
  | [] => k.push text

/-- Rotate for `yank-pop`: the newest entry moves to the back. -/
def rotate (k : KillRing) : KillRing :=
  match k.entries with
  | e :: rest => { k with entries := rest ++ [e] }
  | [] => k

end KillRing

end Leanline
