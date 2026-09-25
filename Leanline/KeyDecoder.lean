import Leanline.Key

/-!
# Decoding terminal input

Turns the raw bytes sent by a terminal into key events: UTF-8 text, control
characters, `ESC`-prefixed Meta keys, CSI and SS3 escape sequences (xterm,
VT100, rxvt, the Linux console, xterm `modifyOtherKeys` and the `CSI u`
protocol) and bracketed paste.

`decode` is a pure function over a byte list. When the bytes seen so far are
a proper prefix of a longer sequence it answers `needMore`; the caller then
waits a short time for further input and, if none arrives, decodes again with
`final := true`, which always makes progress. That is how a lone Escape key
is told apart from the start of an escape sequence.
-/

namespace Leanline

inductive InputEvent where
  | key (k : Key)
  /-- Text delivered through bracketed paste; inserted verbatim. -/
  | paste (text : String)
  deriving DecidableEq, Repr, Inhabited

inductive DecodeResult where
  /-- An event and the bytes after it. -/
  | event (e : InputEvent) (rest : List UInt8)
  /-- A recognised but meaningless sequence (focus reports, unknown CSI). -/
  | skip (rest : List UInt8)
  /-- The input is a proper prefix of a longer sequence. -/
  | needMore
  deriving DecidableEq, Repr, Inhabited

/-- User-defined escape sequences, consulted before the built-in table. -/
abbrev KeySeqTable := List (List UInt8 × Key)

namespace KeyDecoder

def esc : UInt8 := 0x1B

/-- The key for a single byte below 0x80 (other than ESC handling). -/
def asciiKey (b : UInt8) : Key :=
  if b == 0x0D then .plain .enter
  else if b == 0x09 then .plain .tab
  else if b == 0x7F then .plain .backspace
  else if b == 0x1B then .plain .escape
  else if b == 0x00 then Key.ctrl ' '
  else if b < 0x1B then ⟨.char (Char.ofNat (b.toNat + 0x60)), { ctrl := true }⟩
  else if b < 0x20 then ⟨.char (Char.ofNat (b.toNat + 0x40)), { ctrl := true }⟩
  else .char (Char.ofNat b.toNat)

def replacementChar : Char := '�'

def isCont (b : UInt8) : Bool := b &&& 0xC0 == 0x80

/-- Decode one UTF-8 scalar. `none` means the sequence is incomplete. -/
def utf8 (b : UInt8) (rest : List UInt8) : Option (Char × List UInt8) :=
  let n := b.toNat
  let need := if n < 0xC2 then 0 else if n < 0xE0 then 1 else if n < 0xF0 then 2 else if n < 0xF5 then 3 else 0
  if need == 0 then some (replacementChar, rest)
  else
    let conts := rest.take need
    if conts.length < need then
      if conts.all isCont then none else some (replacementChar, rest)
    else if !conts.all isCont then some (replacementChar, rest)
    else
      let lead := n &&& (if need == 1 then 0x1F else if need == 2 then 0x0F else 0x07)
      let cp := conts.foldl (fun acc c => acc * 64 + (c.toNat &&& 0x3F)) lead
      let minCp := if need == 1 then 0x80 else if need == 2 then 0x800 else 0x10000
      if cp < minCp || cp > 0x10FFFF || (0xD800 ≤ cp && cp ≤ 0xDFFF) then some (replacementChar, rest)
      else some (Char.ofNat cp, rest.drop need)

/-- Lossy UTF-8 decoding of a complete byte string. -/
def decodeUtf8 (bs : List UInt8) : List Char := go bs.length bs
where
  -- Every step consumes at least one byte, so the length is enough fuel.
  go : Nat → List UInt8 → List Char
    | 0, _ => []
    | _, [] => []
    | fuel + 1, b :: rest =>
      if b < 0x80 then Char.ofNat b.toNat :: go fuel rest
      else match utf8 b rest with
        | some (c, rest') => c :: go fuel rest'
        | none => [replacementChar]

/-- Modifiers from an xterm modifier parameter (`1 + bitmask`). -/
def modsOf (p : Nat) : Modifiers :=
  let m := p - 1
  { shift := m % 2 == 1, alt := (m / 2) % 2 == 1 || (m / 8) % 2 == 1, ctrl := (m / 4) % 2 == 1 }

def applyMods (mods : Modifiers) (k : Key) : Key :=
  Key.normalize { k with mods := { ctrl := k.mods.ctrl || mods.ctrl, alt := k.mods.alt || mods.alt,
                                   shift := k.mods.shift || mods.shift } }

/-- Key for a Unicode code point reported by `CSI u` or `modifyOtherKeys`. -/
def codepointKey (cp : Nat) : Key :=
  if cp == 13 then .plain .enter
  else if cp == 9 then .plain .tab
  else if cp == 27 then .plain .escape
  else if cp == 127 || cp == 8 then .plain .backspace
  else if cp < 0x20 then asciiKey cp.toUInt8
  else .char (Char.ofNat cp)

def splitSemis : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: rest =>
    if b == 0x3B then [] :: splitSemis rest
    else match splitSemis rest with
      | g :: gs => (b :: g) :: gs
      | [] => [[b]]

/-- Leading decimal digits of a parameter (sub-parameters after `:` are ignored). -/
def leadingNumber (g : List UInt8) : Nat :=
  (g.takeWhile fun d => 0x30 ≤ d && d ≤ 0x39).foldl (fun acc d => acc * 10 + (d.toNat - 0x30)) 0

/-- Parse `;`-separated decimal parameters. Empty parameters read as 1. -/
def params (bs : List UInt8) : List Nat :=
  if bs.isEmpty then [] else (splitSemis bs).map fun g => if g.isEmpty then 1 else leadingNumber g

def tildeKey (n : Nat) : Option BaseKey :=
  match n with
  | 1 | 7 => some .home
  | 2 => some .insert
  | 3 => some .delete
  | 4 | 8 => some .end
  | 5 => some .pageUp
  | 6 => some .pageDown
  | 11 => some (.fn 1) | 12 => some (.fn 2) | 13 => some (.fn 3) | 14 => some (.fn 4)
  | 15 => some (.fn 5) | 17 => some (.fn 6) | 18 => some (.fn 7) | 19 => some (.fn 8)
  | 20 => some (.fn 9) | 21 => some (.fn 10) | 23 => some (.fn 11) | 24 => some (.fn 12)
  | _ => none

def letterKey (c : UInt8) : Option BaseKey :=
  if c == 0x41 then some .up else if c == 0x42 then some .down
  else if c == 0x43 then some .right else if c == 0x44 then some .left
  else if c == 0x48 then some .home else if c == 0x46 then some .end
  else if c == 0x50 then some (.fn 1) else if c == 0x51 then some (.fn 2)
  else if c == 0x52 then some (.fn 3) else if c == 0x53 then some (.fn 4)
  else if c == 0x45 then some .home  -- keypad 5 / "begin"
  else none

/-- Interpret a complete CSI sequence with parameter bytes `ps` and final byte `f`. -/
def csiKey (ps : List UInt8) (f : UInt8) : Option Key :=
  let nums := params ps
  let mods := modsOf (nums[1]?.getD 1)
  if f == 0x7E then  -- '~'
    match nums with
    | 27 :: m :: cp :: _ => some (applyMods (modsOf m) (codepointKey cp))
    | n :: _ => (tildeKey n).map fun b => applyMods mods (.plain b)
    | [] => none
  else if f == 0x75 then  -- 'u'
    match nums with
    | cp :: _ => some (applyMods mods (codepointKey cp))
    | [] => none
  else if f == 0x5A then some ⟨.tab, { shift := true }⟩  -- 'Z' back-tab
  else if 0x61 ≤ f && f ≤ 0x64 then  -- rxvt shift-arrows: ESC [ a..d
    (letterKey (f - 0x20)).map fun b => ⟨b, { shift := true }⟩
  else (letterKey f).map fun b => applyMods mods (.plain b)

def pasteEnd : List UInt8 := [0x1B, 0x5B, 0x32, 0x30, 0x31, 0x7E]

/-- Split at the first occurrence of `sep`. -/
def breakOn (sep : List UInt8) : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | l@(b :: rest) =>
    if sep.isPrefixOf l then some ([], l.drop sep.length)
    else (breakOn sep rest).map fun (pre, post) => (b :: pre, post)

/-- Normalise line endings in pasted text to `\n`. -/
def normalizeNewlines : List Char → List Char
  | '\r' :: '\n' :: rest => '\n' :: normalizeNewlines rest
  | '\r' :: rest => '\n' :: normalizeNewlines rest
  | c :: rest => c :: normalizeNewlines rest
  | [] => []

def pasteText (bs : List UInt8) : String := String.ofList (normalizeNewlines (decodeUtf8 bs))

/-- Split a CSI body into parameter/intermediate bytes and the final byte. -/
def csiSplit : List UInt8 → Option (List UInt8 × UInt8 × List UInt8)
  | [] => none
  | b :: rest =>
    if 0x40 ≤ b && b ≤ 0x7E then some ([], b, rest)
    else if 0x20 ≤ b && b ≤ 0x3F then (csiSplit rest).map fun (ps, f, r) => (b :: ps, f, r)
    else some ([], 0, b :: rest)  -- malformed: final byte 0 is never a key

/-- Decode a single character or control key (no escape sequences). -/
def decodeChar (final : Bool) (b : UInt8) (rest : List UInt8) : DecodeResult :=
  if b < 0x80 then .event (.key (asciiKey b)) rest
  else match utf8 b rest with
    | some (c, rest') => .event (.key (.char c)) rest'
    | none => if final then .event (.key (.char replacementChar)) (rest.dropWhile isCont) else .needMore

/-- Decode everything that follows an ESC byte. -/
def decodeEscape (final : Bool) (rest : List UInt8) : DecodeResult :=
  match rest with
  | [] => if final then .event (.key (.plain .escape)) [] else .needMore
  | 0x5B :: body =>  -- CSI
    match body with
    | 0x5B :: c :: after =>  -- Linux console F1..F5: ESC [ [ A..E
      if 0x41 ≤ c && c ≤ 0x45 then .event (.key (.plain (.fn (c.toNat - 0x40)))) after
      else .skip after
    | [0x5B] => if final then .event (.key (Key.alt '[')) [0x5B] else .needMore
    | _ =>
      match csiSplit body with
      | none => if final then .event (.key (Key.alt '[')) body else .needMore
      | some (ps, f, after) =>
        if f == 0x7E && params ps == [200] then
          match breakOn pasteEnd after with
          | some (text, after') => .event (.paste (pasteText text)) after'
          | none => if final then .event (.paste (pasteText after)) [] else .needMore
        else match csiKey ps f with
          | some k => .event (.key k) after
          | none => .skip after
  | 0x4F :: body =>  -- SS3
    match body with
    | [] => if final then .event (.key (Key.alt 'O')) [] else .needMore
    | c :: after =>
      if c == 0x4D then .event (.key (.plain .enter)) after
      else if 0x61 ≤ c && c ≤ 0x64 then
        match letterKey (c - 0x20) with
        | some b => .event (.key ⟨b, { ctrl := true }⟩) after
        | none => .skip after
      else match letterKey c with
        | some b => .event (.key (.plain b)) after
        | none => .skip after
  | 0x1B :: body =>  -- ESC ESC ... : Meta applied to an escape sequence, or M-Esc
    match body with
    | [] => if final then .event (.key (Key.plain .escape).withAlt) [] else .needMore
    | 0x5B :: _ | 0x4F :: _ =>
      match decodeEscape final body with
      | .event (.key k) r => .event (.key k.withAlt) r
      | other => other
    | _ => .event (.key (Key.plain .escape).withAlt) body
  | b :: after =>
    match decodeChar final b after with
    | .event (.key k) r => .event (.key k.withAlt) r
    | other => other

/-- Decode the next event from `bytes`, consulting user-defined sequences first. -/
def decode (table : KeySeqTable := []) (final : Bool := false) (bytes : List UInt8) : DecodeResult :=
  match table.find? (fun (seq, _) => !seq.isEmpty && seq.isPrefixOf bytes) with
  | some (seq, k) => .event (.key k) (bytes.drop seq.length)
  | none =>
    if !final && table.any (fun (seq, _) => bytes.isPrefixOf seq && bytes.length < seq.length && !bytes.isEmpty)
    then .needMore
    else match bytes with
      | [] => .needMore
      | 0x1B :: rest => decodeEscape final rest
      | b :: rest => decodeChar final b rest

/-- Decode as many complete events as possible; returns them and the leftover
bytes (a proper prefix of an unfinished sequence). -/
def decodeAll (table : KeySeqTable) (final : Bool) (bytes : List UInt8) : List InputEvent × List UInt8 :=
  go bytes.length bytes []
where
  go (fuel : Nat) (bs : List UInt8) (acc : List InputEvent) : List InputEvent × List UInt8 :=
    match fuel with
    | 0 => (acc.reverse, bs)
    | fuel + 1 =>
      match decode table final bs with
      | .event e rest => go fuel rest (e :: acc)
      | .skip rest => go fuel rest acc
      | .needMore => (acc.reverse, bs)

end KeyDecoder

end Leanline
