import Leanline

/-!
# Theorems: decoding terminal input

Concrete escape sequences from common terminals, plus two general results:
printable ASCII is always read as itself, and once the escape timeout has
expired (`final := true`) decoding always makes progress, so the reader can
never get stuck on a partial sequence.
-/

namespace Leanline.Tests

open KeyDecoder

def dec (bytes : List UInt8) : DecodeResult := decode [] false bytes
def decFinal (bytes : List UInt8) : DecodeResult := decode [] true bytes
def key (k : Key) (rest : List UInt8 := []) : DecodeResult := .event (.key k) rest

/-! ## Plain characters -/

example : dec [0x61] = key (Key.char 'a') := by decide
example : dec [0x61, 0x62] = key (Key.char 'a') [0x62] := by decide
example : dec [0x0D] = key (.plain .enter) := by decide
example : dec [0x0A] = key (Key.ctrl 'j') := by decide
example : dec [0x09] = key (.plain .tab) := by decide
example : dec [0x7F] = key (.plain .backspace) := by decide
example : dec [0x08] = key (Key.ctrl 'h') := by decide
example : dec [0x01] = key (Key.ctrl 'a') := by decide
example : dec [0x03] = key (Key.ctrl 'c') := by decide
example : dec [0x1F] = key (Key.ctrl '_') := by decide
example : dec [0x00] = key (Key.ctrl ' ') := by decide

/-! ## UTF-8 -/

example : dec [0xC3, 0xA9] = key (Key.char 'é') := by decide
example : dec [0xE2, 0x82, 0xAC] = key (Key.char '€') := by decide
example : dec [0xF0, 0x9F, 0x98, 0x80] = key (Key.char '😀') := by decide
/-- An incomplete multi-byte character waits for the rest… -/
example : dec [0xE2, 0x82] = .needMore := by decide
/-- …unless the timeout expired. -/
example : decFinal [0xE2, 0x82] = key (Key.char '�') := by decide
/-- Invalid bytes become U+FFFD instead of being dropped silently. -/
example : dec [0xFF, 0x61] = key (Key.char '�') [0x61] := by decide
example : dec [0xC0, 0x80] = key (Key.char '�') [0x80] := by decide
example : decodeUtf8 [0x68, 0xC3, 0xA9, 0xE2, 0x82, 0xAC] = ['h', 'é', '€'] := by decide

/-! ## Escape, Meta, and escape sequences -/

/-- A lone ESC is ambiguous until the timeout… -/
example : dec [0x1B] = .needMore := by decide
/-- …after which it is the Escape key. -/
example : decFinal [0x1B] = key (.plain .escape) := by decide
example : dec [0x1B, 0x66] = key (Key.alt 'f') := by decide
example : dec [0x1B, 0x7F] = key ⟨.backspace, { alt := true }⟩ := by decide
example : dec [0x1B, 0x0D] = key ⟨.enter, { alt := true }⟩ := by decide
example : decFinal [0x1B, 0x1B] = key ⟨.escape, { alt := true }⟩ := by decide

-- xterm / VT100 cursor keys, in normal and application mode
example : dec [0x1B, 0x5B, 0x41] = key (.plain .up) := by decide
example : dec [0x1B, 0x5B, 0x42] = key (.plain .down) := by decide
example : dec [0x1B, 0x5B, 0x43] = key (.plain .right) := by decide
example : dec [0x1B, 0x5B, 0x44] = key (.plain .left) := by decide
example : dec [0x1B, 0x4F, 0x41] = key (.plain .up) := by decide
example : dec [0x1B, 0x5B, 0x48] = key (.plain .home) := by decide
example : dec [0x1B, 0x4F, 0x46] = key (.plain .end) := by decide
-- vt220 editing keys
example : dec [0x1B, 0x5B, 0x31, 0x7E] = key (.plain .home) := by decide
example : dec [0x1B, 0x5B, 0x33, 0x7E] = key (.plain .delete) := by decide
example : dec [0x1B, 0x5B, 0x34, 0x7E] = key (.plain .end) := by decide
example : dec [0x1B, 0x5B, 0x35, 0x7E] = key (.plain .pageUp) := by decide
example : dec [0x1B, 0x5B, 0x36, 0x7E] = key (.plain .pageDown) := by decide
-- function keys
example : dec [0x1B, 0x4F, 0x50] = key (.plain (.fn 1)) := by decide
example : dec [0x1B, 0x5B, 0x31, 0x35, 0x7E] = key (.plain (.fn 5)) := by decide
example : dec [0x1B, 0x5B, 0x32, 0x34, 0x7E] = key (.plain (.fn 12)) := by decide
example : dec [0x1B, 0x5B, 0x5B, 0x41] = key (.plain (.fn 1)) := by decide
-- modifiers: xterm `1;5` is Ctrl, `1;3` is Alt, `1;2` is Shift
example : dec [0x1B, 0x5B, 0x31, 0x3B, 0x35, 0x43] = key ⟨.right, { ctrl := true }⟩ := by decide
example : dec [0x1B, 0x5B, 0x31, 0x3B, 0x33, 0x44] = key ⟨.left, { alt := true }⟩ := by decide
example : dec [0x1B, 0x5B, 0x31, 0x3B, 0x36, 0x41] = key ⟨.up, { ctrl := true, shift := true }⟩ := by decide
example : dec [0x1B, 0x5B, 0x33, 0x3B, 0x35, 0x7E] = key ⟨.delete, { ctrl := true }⟩ := by decide
-- rxvt
example : dec [0x1B, 0x4F, 0x64] = key ⟨.left, { ctrl := true }⟩ := by decide
example : dec [0x1B, 0x5B, 0x61] = key ⟨.up, { shift := true }⟩ := by decide
-- back-tab
example : dec [0x1B, 0x5B, 0x5A] = key ⟨.tab, { shift := true }⟩ := by decide
-- Meta applied to an escape sequence
example : dec [0x1B, 0x1B, 0x5B, 0x44] = key ⟨.left, { alt := true }⟩ := by decide
-- `CSI u` (kitty, foot, WezTerm) and xterm `modifyOtherKeys`
example : dec [0x1B, 0x5B, 0x39, 0x37, 0x3B, 0x35, 0x75] = key (Key.ctrl 'a') := by decide
example : dec [0x1B, 0x5B, 0x31, 0x33, 0x3B, 0x33, 0x75] = key ⟨.enter, { alt := true }⟩ := by decide
example : dec [0x1B, 0x5B, 0x32, 0x37, 0x3B, 0x33, 0x3B, 0x39, 0x37, 0x7E] = key (Key.alt 'a') := by decide
/-- Keys a terminal cannot tell apart are normalised: `C-i` is Tab. -/
example : dec [0x1B, 0x5B, 0x32, 0x37, 0x3B, 0x35, 0x3B, 0x31, 0x30, 0x35, 0x7E] = key (.plain .tab) := by decide
-- incomplete sequences wait; focus reports are skipped
example : dec [0x1B, 0x5B] = .needMore := by decide
example : dec [0x1B, 0x5B, 0x31, 0x3B] = .needMore := by decide
example : decFinal [0x1B, 0x5B] = key (Key.alt '[') := by decide
example : dec [0x1B, 0x5B, 0x49, 0x61] = .skip [0x61] := by decide

/-! ## Bracketed paste -/

/-- Pasted text arrives as one event, with its newline intact and no command
interpretation (the Enter inside does not accept the line). -/
example : dec ([0x1B, 0x5B, 0x32, 0x30, 0x30, 0x7E] ++ [0x6C, 0x73, 0x0D, 0x0A, 0x63, 0x64] ++
    [0x1B, 0x5B, 0x32, 0x30, 0x31, 0x7E, 0x61]) = .event (.paste "ls\ncd") [0x61] := by decide
/-- An unfinished paste waits for its end marker. -/
example : dec [0x1B, 0x5B, 0x32, 0x30, 0x30, 0x7E, 0x61, 0x62, 0x63] = .needMore := by decide

/-! ## User-defined sequences -/

example : decode [([0x1B, 0x5B, 0x39, 0x39, 0x7E], Key.ctrl 'x')] false [0x1B, 0x5B, 0x39, 0x39, 0x7E] =
    key (Key.ctrl 'x') := by decide
example : decode [([0x1B, 0x5B, 0x39, 0x39, 0x7E], Key.ctrl 'x')] false [0x1B, 0x5B, 0x39] = .needMore := by decide

/-! ## Decoding several events -/

example : decodeAll [] false [0x61, 0x1B, 0x5B, 0x41, 0x62, 0x1B] =
    ([.key (Key.char 'a'), .key (.plain .up), .key (Key.char 'b')], [0x1B]) := by decide

/-! ## General properties -/

theorem asciiKey_printable :
    ∀ i : Fin 95, asciiKey (UInt8.ofNat (i.val + 32)) = Key.char (Char.ofNat (i.val + 32)) := by
  decide

/-- Input not starting with ESC is decoded as a single character or control key. -/
theorem decode_nonEsc (final : Bool) (b : UInt8) (rest : List UInt8) (hb : b ≠ 0x1B) :
    decode [] final (b :: rest) = decodeChar final b rest := by
  unfold decode
  simp only [List.find?_nil, List.any_nil, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem decode_esc (final : Bool) (rest : List UInt8) :
    decode [] final (0x1B :: rest) = decodeEscape final rest := by
  unfold decode
  simp

/-- Every ASCII byte other than ESC is read as a single key, whatever follows. -/
theorem decode_ascii (b : UInt8) (rest : List UInt8) (hne : b ≠ 0x1B) (hlt : b < 0x80) :
    dec (b :: rest) = key (asciiKey b) rest := by
  rw [dec, decode_nonEsc false b rest hne]
  simp [decodeChar, hlt, key]

/-- Every printable ASCII byte is read as that character, whatever follows. -/
theorem decode_printable (i : Fin 95) (rest : List UInt8) :
    dec (UInt8.ofNat (i.val + 32) :: rest) = key (Key.char (Char.ofNat (i.val + 32))) rest := by
  rw [decode_ascii _ _ (by revert i; decide) (by revert i; decide), asciiKey_printable]

theorem decodeChar_final_progress (b : UInt8) (rest : List UInt8) : decodeChar true b rest ≠ .needMore := by
  unfold decodeChar
  split
  · simp
  · split <;> simp

theorem decodeEscape_final_progress (rest : List UInt8) : decodeEscape true rest ≠ .needMore := by
  induction rest with
  | nil => simp [decodeEscape]
  | cons b tl ih =>
    unfold decodeEscape
    repeat' split
    all_goals simp_all [decodeChar_final_progress]

/-- After the escape timeout, decoding never waits for more input: every
non-empty input yields an event or is skipped. -/
theorem decode_final_progress (bytes : List UInt8) (h : bytes ≠ []) : decode [] true bytes ≠ .needMore := by
  cases bytes with
  | nil => contradiction
  | cons b rest =>
    by_cases hb : b = 0x1B
    · subst hb; rw [decode_esc]; exact decodeEscape_final_progress rest
    · rw [decode_nonEsc true b rest hb]; exact decodeChar_final_progress b rest

/-- ASCII text decodes to itself. -/
theorem decodeUtf8_ascii (cs : List Char) (h : ∀ c ∈ cs, c.toNat < 128) :
    decodeUtf8 (cs.map fun c => c.toNat.toUInt8) = cs := by
  unfold decodeUtf8
  rw [List.length_map]
  induction cs with
  | nil => simp [decodeUtf8.go]
  | cons c cs ih =>
    have hc := h c (by simp)
    have hrest : ∀ d ∈ cs, d.toNat < 128 := fun d hd => h d (by simp [hd])
    simp only [List.map_cons, List.length_cons, decodeUtf8.go]
    have hlt : c.toNat.toUInt8 < 0x80 := by
      rw [UInt8.lt_iff_toNat_lt]; simp; omega
    have hnat : c.toNat.toUInt8.toNat = c.toNat := by simp; omega
    simp only [hlt, ↓reduceIte, ih hrest, hnat, Char.ofNat_toNat]

end Leanline.Tests
