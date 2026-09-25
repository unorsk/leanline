import Leanline

/-!
# Theorems: graphemes and the line buffer

General properties of the zipper: segmentation loses nothing, motions never
change the text, insertion and deletion are inverse, kills can be yanked
back, and `transpose` only permutes.
-/

namespace Leanline.Tests

open LineBuffer

/-! ## Grapheme segmentation is lossless -/

theorem charsOf_append (a b : List Grapheme) : charsOf (a ++ b) = charsOf a ++ charsOf b := by
  simp [charsOf]

theorem charsOf_pushChar (acc : List Grapheme) (c : Char) :
    charsOf (pushChar acc c).reverse = charsOf acc.reverse ++ [c] := by
  cases acc with
  | nil => simp [pushChar, charsOf, Grapheme.toList]
  | cons g rest =>
    simp only [pushChar]
    split <;> simp [charsOf, Grapheme.toList]

theorem charsOf_foldl (cs : List Char) (acc : List Grapheme) :
    charsOf (cs.foldl pushChar acc).reverse = charsOf acc.reverse ++ cs := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih => simp [List.foldl, ih, charsOf_pushChar]

/-- Splitting text into graphemes and flattening it again gives back the text. -/
theorem charsOf_graphemes (cs : List Char) : charsOf (graphemes cs) = cs := by
  simpa [graphemes, charsOf] using charsOf_foldl cs []

/-- A buffer made from a string holds exactly that string. -/
theorem ofString_toString (s : String) : (LineBuffer.ofString s).toString = s := by
  simp [LineBuffer.ofString, LineBuffer.ofLists, LineBuffer.toString, LineBuffer.chars,
    LineBuffer.graphemes, graphemesOf, charsOf_graphemes]

theorem ofParts_toString (l r : String) : (LineBuffer.ofParts l r).toString = l ++ r := by
  simp [LineBuffer.ofParts, LineBuffer.ofLists, LineBuffer.toString, LineBuffer.chars,
    LineBuffer.graphemes, graphemesOf, charsOf_append, charsOf_graphemes]

/-! ## Motions preserve the text -/

/-- A motion moves the cursor without touching the text. -/
def IsMotion (f : LineBuffer → LineBuffer) : Prop := ∀ b, (f b).graphemes = b.graphemes

@[simp] theorem graphemes_mk (l r : List Grapheme) : (LineBuffer.mk l r).graphemes = l.reverse ++ r := rfl

theorem moveLeft_motion : IsMotion moveLeft := by
  intro ⟨l, r⟩; cases l <;> simp [moveLeft]

theorem moveRight_motion : IsMotion moveRight := by
  intro ⟨l, r⟩; cases r <;> simp [moveRight]

theorem moveToStart_motion : IsMotion moveToStart := by
  intro ⟨l, r⟩; simp [moveToStart]

theorem moveToEnd_motion : IsMotion moveToEnd := by
  intro ⟨l, r⟩; simp [moveToEnd]

theorem moveTo_motion (n : Nat) : IsMotion (moveTo n) := by
  intro b; simp [moveTo, LineBuffer.graphemes]

theorem IsMotion.comp {f g : LineBuffer → LineBuffer} (hf : IsMotion f) (hg : IsMotion g) :
    IsMotion (g ∘ f) := by
  intro b; simp [hg (f b), hf b]

theorem iterate_motion {f : LineBuffer → LineBuffer} (hf : IsMotion f) (n : Nat) : IsMotion (iterate n f) := by
  induction n with
  | zero => intro b; rfl
  | succ n ih => intro b; simp [iterate, ih (f b), hf b]

theorem spanLeft_spec (p : Grapheme → Bool) (l r : List Grapheme) :
    (spanLeft p l r).1.reverse ++ (spanLeft p l r).2 = l.reverse ++ r := by
  induction l generalizing r with
  | nil => simp [spanLeft]
  | cons g l ih => unfold spanLeft; split <;> simp [ih]

theorem spanRight_spec (p : Grapheme → Bool) (l r : List Grapheme) :
    (spanRight p l r).1.reverse ++ (spanRight p l r).2 = l.reverse ++ r := by
  induction r generalizing l with
  | nil => simp [spanRight]
  | cons g r ih => unfold spanRight; split <;> simp [ih]

theorem skipLeft_motion (p : Grapheme → Bool) : IsMotion (skipLeft p) := by
  intro ⟨l, r⟩; simp [skipLeft, spanLeft_spec]

theorem skipRight_motion (p : Grapheme → Bool) : IsMotion (skipRight p) := by
  intro ⟨l, r⟩; simp [skipRight, spanRight_spec]

theorem wordLeft_motion : IsMotion wordLeft := fun b => by
  simp [wordLeft, skipLeft_motion _ _]

theorem wordRight_motion : IsMotion wordRight := fun b => by
  simp [wordRight, skipRight_motion _ _]

theorem bigWordLeft_motion : IsMotion bigWordLeft := fun b => by
  simp [bigWordLeft, skipLeft_motion _ _]

theorem viWordForward_motion (cls : Grapheme → Nat) : IsMotion (viWordForward cls) := by
  intro b
  unfold viWordForward
  split
  · rfl
  · split <;> simp [skipRight_motion _ _]

theorem viWordBackward_motion (cls : Grapheme → Nat) : IsMotion (viWordBackward cls) := by
  intro b
  simp only [viWordBackward]
  split <;> simp [skipLeft_motion _ _]

theorem viWordEnd_motion (cls : Grapheme → Nat) : IsMotion (viWordEnd cls) := by
  intro b
  simp only [viWordEnd]
  split <;> simp [moveLeft_motion _, skipRight_motion _ _, moveRight_motion _]

theorem viClamp_motion : IsMotion viClamp := by
  intro b
  unfold viClamp
  split <;> simp [moveLeft_motion _]

/-! ## Cursor positions -/

theorem length_eq (b : LineBuffer) : b.length = b.graphemes.length := by
  simp [LineBuffer.length, LineBuffer.graphemes]

theorem pos_le_length (b : LineBuffer) : b.pos ≤ b.length := by
  simp [LineBuffer.pos, LineBuffer.length]

@[simp] theorem pos_moveToStart (b : LineBuffer) : b.moveToStart.pos = 0 := rfl

@[simp] theorem pos_moveToEnd (b : LineBuffer) : b.moveToEnd.pos = b.length := by
  simp [moveToEnd, LineBuffer.pos, LineBuffer.length, Nat.add_comm]

theorem pos_moveTo (b : LineBuffer) (n : Nat) : (b.moveTo n).pos = min n b.length := by
  simp [moveTo, LineBuffer.pos, length_eq]

theorem moveLeft_moveRight (b : LineBuffer) (h : b.after ≠ []) : b.moveRight.moveLeft = b := by
  obtain ⟨l, r⟩ := b
  cases r with
  | nil => contradiction
  | cons g r => rfl

theorem moveRight_moveLeft (b : LineBuffer) (h : b.before ≠ []) : b.moveLeft.moveRight = b := by
  obtain ⟨l, r⟩ := b
  cases l with
  | nil => contradiction
  | cons g l => rfl

/-! ## Insertion and deletion -/

theorem graphemes_insert (b : LineBuffer) (g : Grapheme) :
    (b.insert g).graphemes = b.before.reverse ++ g :: b.after := by
  simp [LineBuffer.insert, LineBuffer.graphemes]

theorem graphemes_insertList (b : LineBuffer) (gs : List Grapheme) :
    (b.insertList gs).graphemes = b.before.reverse ++ gs ++ b.after := by
  simp [insertList, LineBuffer.graphemes]

theorem pos_insertList (b : LineBuffer) (gs : List Grapheme) :
    (b.insertList gs).pos = b.pos + gs.length := by
  simp [insertList, LineBuffer.pos, Nat.add_comm]

/-- Backspace undoes the insertion of a grapheme. -/
theorem deleteBackward_insert (b : LineBuffer) (g : Grapheme) : (b.insert g).deleteBackward = b := by
  cases b; rfl

/-- Typing a character puts exactly that character at the cursor, whether it
starts a new grapheme or combines with the previous one. -/
theorem chars_insertChar (b : LineBuffer) (c : Char) :
    (b.insertChar c).chars = charsOf b.before.reverse ++ c :: charsOf b.after := by
  obtain ⟨l, r⟩ := b
  cases l with
  | nil => simp [insertChar, LineBuffer.insert, LineBuffer.chars, charsOf, Grapheme.ofChar, Grapheme.toList]
  | cons g l =>
    simp only [insertChar]
    split <;> simp [LineBuffer.insert, LineBuffer.chars, charsOf, Grapheme.ofChar, Grapheme.toList]

/-! ## Killing and yanking -/

/-- Deleting a region splits the text into the kept parts and the deleted part. -/
theorem deleteTo_spec (b : LineBuffer) (p : Nat) :
    (b.deleteTo p).1.before.reverse ++ (b.deleteTo p).2 ++ (b.deleteTo p).1.after = b.graphemes := by
  simp only [deleteTo, List.reverse_reverse]
  have hle : min b.pos p ≤ max b.pos p := by omega
  generalize b.graphemes = gs
  generalize min b.pos p = lo at *
  generalize max b.pos p = hi at *
  obtain ⟨k, rfl⟩ : ∃ k, hi = lo + k := ⟨hi - lo, by omega⟩
  rw [Nat.add_sub_cancel_left, List.append_assoc, ← List.drop_drop, List.take_append_drop,
    List.take_append_drop]

/-- Yanking a kill at the place it was taken from restores the text. -/
theorem yank_after_kill (b : LineBuffer) (p : Nat) :
    ((b.deleteTo p).1.insertList (b.deleteTo p).2).graphemes = b.graphemes := by
  rw [graphemes_insertList]
  exact deleteTo_spec b p

/-- The cursor lands at the start of the deleted region. -/
theorem pos_deleteTo (b : LineBuffer) (p : Nat) :
    (b.deleteTo p).1.pos = min (min b.pos p) b.length := by
  simp [deleteTo, LineBuffer.pos, length_eq]

theorem length_deleteTo (b : LineBuffer) (p : Nat) :
    (b.deleteTo p).1.length + (b.deleteTo p).2.length = b.length := by
  have h := congrArg List.length (deleteTo_spec b p)
  simp only [List.length_append, List.length_reverse] at h
  rw [length_eq b, ← h]
  simp only [LineBuffer.length]
  omega

/-! ## Transposition -/

theorem transpose_perm (b : LineBuffer) : b.transpose.graphemes.Perm b.graphemes := by
  obtain ⟨l, r⟩ := b
  match l, r with
  | [], _ => exact List.Perm.refl _
  | [_], [] => exact List.Perm.refl _
  | a :: c :: l, [] =>
    simp only [transpose, graphemes_mk, List.reverse_cons, List.append_nil, List.append_assoc,
      List.singleton_append]
    exact List.Perm.append_left _ (List.Perm.swap _ _ _)
  | a :: l, c :: r =>
    simp only [transpose, graphemes_mk, List.reverse_cons, List.append_assoc, List.cons_append]
    exact List.Perm.append_left _ (List.Perm.swap _ _ _)

theorem length_transpose (b : LineBuffer) : b.transpose.length = b.length := by
  rw [length_eq, length_eq]
  exact (transpose_perm b).length_eq

/-- At the end of the line, transposing twice changes nothing. -/
theorem transpose_transpose_atEnd (b : LineBuffer) (h : b.after = []) : b.transpose.transpose = b := by
  obtain ⟨l, r⟩ := b
  subst h
  match l with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

end Leanline.Tests
