import Leanline

/-!
# Theorems: Unicode, graphemes and the kill ring
-/

namespace Leanline.Tests

open Unicode

/-! ## Display width -/

example : charWidth 'a' = 1 := by decide +kernel
example : charWidth 'é' = 1 := by decide +kernel
example : charWidth '日' = 2 := by decide +kernel
example : charWidth '한' = 2 := by decide +kernel
example : charWidth 'Ａ' = 2 := by decide +kernel
example : charWidth '😀' = 2 := by decide +kernel
example : charWidth '\u0301' = 0 := by decide +kernel
example : charWidth '\u200D' = 0 := by decide +kernel
example : charWidth '\x07' = 0 := by decide +kernel

/-- Every printable ASCII character is one column wide. -/
theorem ascii_width : ∀ i : Fin 95, charWidth (Char.ofNat (i.val + 32)) = 1 := by decide +kernel

/-- Every CJK unified ideograph in the basic block is two columns wide. -/
theorem cjk_width (c : Char) (h1 : 0x4E00 ≤ c.toNat) (h2 : c.toNat ≤ 0x9FFF) : charWidth c = 2 := by
  have hctl : isControl c = false := by simp [isControl]; omega
  have hcomb : isCombining c = false := by
    simp only [isCombining, combiningRanges, inRanges]; simp; omega
  have hwide : isWide c = true := by
    simp only [isWide, wideRanges, inRanges]; simp; omega
  simp [charWidth, hctl, hcomb, hwide]

/-! ## Graphemes -/

example : (graphemesOf "e\u0301").length = 1 := by decide +kernel
example : widthOf (graphemesOf "e\u0301") = 1 := by decide +kernel
/-- Emoji with a skin-tone modifier. -/
example : (graphemesOf "👍🏽").length = 1 := by decide +kernel
/-- A family emoji joined with zero-width joiners. -/
example : (graphemesOf "👨\u200D👩\u200D👧").length = 1 := by decide +kernel
/-- Flags are pairs of regional indicators… -/
example : (graphemesOf "🇫🇷🇩🇪").length = 2 := by decide +kernel
example : widthOf (graphemesOf "🇫🇷") = 2 := by decide +kernel
/-- …and variation selectors attach to their base. -/
example : (graphemesOf "❤\uFE0F").length = 1 := by decide +kernel
example : widthOf (graphemesOf "❤\uFE0F") = 2 := by decide +kernel
example : (graphemesOf "abc").length = 3 := by decide +kernel

/-! ## Word characters and case -/

example : isWordChar 'a' ∧ isWordChar '_' ∧ isWordChar '7' ∧ isWordChar 'ж' ∧ isWordChar '日' := by decide +kernel
example : ¬isWordChar ' ' ∧ ¬isWordChar '.' ∧ ¬isWordChar '/' ∧ ¬isWordChar '—' := by decide +kernel

theorem ascii_case_roundtrip : ∀ i : Fin 26,
    toLower (toUpper (Char.ofNat (97 + i.val))) = Char.ofNat (97 + i.val) ∧
    toUpper (Char.ofNat (97 + i.val)) = Char.ofNat (65 + i.val) := by decide +kernel

theorem cyrillic_case_roundtrip : ∀ i : Fin 32,
    toLower (toUpper (Char.ofNat (0x430 + i.val))) = Char.ofNat (0x430 + i.val) := by decide +kernel

theorem latin1_case_roundtrip : ∀ i : Fin 31, i.val ≠ 23 →
    toLower (toUpper (Char.ofNat (0xE0 + i.val))) = Char.ofNat (0xE0 + i.val) := by decide +kernel

example : toUpper 'é' = 'É' ∧ toUpper 'ω' = 'Ω' ∧ toUpper 'ж' = 'Ж' ∧ toUpper 'ё' = 'Ё' := by decide +kernel
example : toLower 'Ä' = 'ä' ∧ toLower 'Σ' = 'σ' ∧ toUpper '1' = '1' := by decide +kernel

/-! ## Kill ring -/

theorem push_capacity (k : KillRing) (t : List Grapheme) (h : k.entries.length ≤ k.capacity) :
    (k.push t).entries.length ≤ k.capacity := by
  unfold KillRing.push
  split
  · exact h
  · simp; omega

theorem rotate_perm (k : KillRing) : (k.rotate).entries.Perm k.entries := by
  unfold KillRing.rotate
  split
  · rename_i e rest h; rw [h]; exact List.perm_append_singleton e rest
  · exact List.Perm.refl _

theorem push_top (k : KillRing) (t : List Grapheme) (ht : t ≠ []) (hc : 0 < k.capacity) :
    (k.push t).top? = some t := by
  unfold KillRing.push KillRing.top?
  have : t.isEmpty = false := by cases t <;> simp_all
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨n, hn⟩ : ∃ n, k.capacity = n + 1 := ⟨k.capacity - 1, by omega⟩
  simp [hn]

example : (KillRing.push [] {}).entries = [] := by decide +kernel
example : ((KillRing.push (graphemesOf "a") {}).merge (graphemesOf "b") false).top? = some (graphemesOf "ab") := by decide +kernel
example : ((KillRing.push (graphemesOf "a") {}).merge (graphemesOf "b") true).top? = some (graphemesOf "ba") := by decide +kernel
example : ((KillRing.push (graphemesOf "2") (KillRing.push (graphemesOf "1") {})).rotate).top? = some (graphemesOf "1") := by
  decide
example : ((List.range 100).foldl (fun k i => k.push [Grapheme.ofChar (Char.ofNat (65 + i % 26))]) ({} : KillRing)).entries.length
    = 60 := by decide +kernel

end Leanline.Tests
