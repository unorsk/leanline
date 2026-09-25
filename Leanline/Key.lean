import Leanline.Text

/-!
# Keys

A `Key` is a base key plus modifiers. Control characters are represented as
`ctrl` plus a lowercase letter or symbol, never as raw control codes, and
keys that terminals cannot distinguish (`C-i` and Tab, `C-m` and Enter,
`C-[` and Escape) are normalised to one representation.
-/

namespace Leanline

inductive BaseKey where
  | char (c : Char)
  | fn (n : Nat)
  | left | right | up | down
  | home | «end» | pageUp | pageDown
  | insert | delete | backspace
  | enter | tab | escape
  deriving DecidableEq, Repr, Inhabited, Hashable

structure Modifiers where
  ctrl : Bool := false
  alt : Bool := false
  shift : Bool := false
  deriving DecidableEq, Repr, Inhabited, Hashable

structure Key where
  base : BaseKey
  mods : Modifiers := {}
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Key

def plain (b : BaseKey) : Key := ⟨b, {}⟩

/-- A printable character. -/
def char (c : Char) : Key := plain (.char c)

/-- Canonical form: fold control aliases onto the keys they are sent as. -/
def normalize (k : Key) : Key :=
  match k.base, k.mods.ctrl with
  | .char c, true =>
    let c := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
    let other := { k.mods with ctrl := false }
    if c == 'i' then ⟨.tab, other⟩
    else if c == 'm' then ⟨.enter, other⟩
    else if c == '[' then ⟨.escape, other⟩
    else if c == '?' then ⟨.backspace, other⟩
    else ⟨.char c, k.mods⟩
  | _, _ => k

/-- `C-c` for a letter or symbol `c`. -/
def ctrl (c : Char) : Key := normalize ⟨.char c, { ctrl := true }⟩

/-- `M-c`: Alt (Meta) with a character. -/
def alt (c : Char) : Key := ⟨.char c, { alt := true }⟩

def withAlt (k : Key) : Key := { k with mods := { k.mods with alt := true } }
def withCtrl (k : Key) : Key := normalize { k with mods := { k.mods with ctrl := true } }
def withShift (k : Key) : Key := { k with mods := { k.mods with shift := true } }

/-- The character a key inserts, if it is an unmodified printable key. -/
def printable? (k : Key) : Option Char :=
  match k.base with
  | .char c => if k.mods == {} && c.toNat ≥ 0x20 && c.toNat != 0x7F then some c else none
  | _ => none

def baseName : BaseKey → String
  | .char ' ' => "Space"
  | .char c => c.toString
  | .fn n => s!"F{n}"
  | .left => "Left" | .right => "Right" | .up => "Up" | .down => "Down"
  | .home => "Home" | .end => "End" | .pageUp => "PageUp" | .pageDown => "PageDown"
  | .insert => "Insert" | .delete => "Delete" | .backspace => "Backspace"
  | .enter => "Enter" | .tab => "Tab" | .escape => "Esc"

/-- Emacs-style notation: `C-a`, `M-f`, `C-M-Left`, `S-Tab`. -/
protected def toString (k : Key) : String :=
  (if k.mods.ctrl then "C-" else "") ++ (if k.mods.alt then "M-" else "") ++
  (if k.mods.shift then "S-" else "") ++ baseName k.base

instance : ToString Key := ⟨Key.toString⟩

private def namedKeys : List (String × BaseKey) :=
  [("left", .left), ("right", .right), ("up", .up), ("down", .down),
   ("home", .home), ("end", .end), ("pageup", .pageUp), ("pagedown", .pageDown),
   ("insert", .insert), ("delete", .delete), ("del", .delete),
   ("backspace", .backspace), ("enter", .enter), ("return", .enter), ("ret", .enter),
   ("tab", .tab), ("esc", .escape), ("escape", .escape), ("space", .char ' '),
   ("spc", .char ' ')]

private def parseBase (cs : List Char) : Option BaseKey :=
  match cs with
  | [c] => some (.char c)
  | _ =>
    let l := Text.lower cs
    match namedKeys.lookup (String.ofList l) with
    | some b => some b
    | none =>
      match l with
      | 'f' :: digits => (Text.toNat? digits).map BaseKey.fn
      | _ => none

/-- Parse key notation from characters; `fuel` bounds the modifier prefixes. -/
def parseChars : Nat → List Char → Option Key
  | 0, _ => none
  | fuel + 1, cs =>
    let lower := Text.lower cs
    let tryPrefix (pre : String) (f : Key → Key) : Option Key :=
      if pre.toList.isPrefixOf lower && cs.length > pre.length then
        (parseChars fuel (cs.drop pre.length)).map f
      else none
    (tryPrefix "ctrl-" withCtrl) <|> (tryPrefix "c-" withCtrl) <|>
    (tryPrefix "meta-" withAlt) <|> (tryPrefix "alt-" withAlt) <|> (tryPrefix "m-" withAlt) <|>
    (tryPrefix "shift-" withShift) <|> (tryPrefix "s-" withShift) <|>
    (parseBase cs).map plain

/-- Parse key notation. Accepts Haskeline's `ctrl-a`, `meta-f`, `shift-left`
and Emacs's `C-a`, `M-f`, `S-Tab`, in any combination, plus names such as
`left`, `f5`, `backspace`, `space`. -/
def parse? (s : String) : Option Key := parseChars (s.length + 1) s.toList

/-- Parse a space-separated key sequence such as `"C-x C-e"`. -/
def parseSeq? (s : String) : Option (List Key) :=
  (Text.wordsOf s).mapM parse?

end Key

end Leanline
