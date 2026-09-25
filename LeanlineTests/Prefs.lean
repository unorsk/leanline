import Leanline

/-!
# Theorems: preferences and key names
-/

namespace Leanline.Tests

def sample : String :=
  "-- Haskeline-style preferences\n" ++
  "editMode: Vi\n" ++
  "bellStyle: VisualBell\n" ++
  "maxHistorySize: Just 500\n" ++
  "historyDuplicates: IgnoreConsecutive\n" ++
  "completionType: MenuCompletion\n" ++
  "completionPaging: False\n" ++
  "completionPromptLimit: Nothing\n" ++
  "listCompletionsImmediately: False\n" ++
  "bind: ctrl-t up\n" ++
  "keyseq: xterm \"\\ESC[1;5D\" ctrl-left\n" ++
  "keyseq: \"\\e[99~\" f12\n" ++
  "# Leanline extensions\n" ++
  "historySuggestions: yes\n" ++
  "prefix-history-search: on\n" ++
  "keySeqTimeout: 30\n"

set_option maxRecDepth 100000 in
/-- Every setting of the sample file is understood (one evaluation of the
parser checks them all). -/
example :
    let (p, errors) := Prefs.parse sample
    errors = [] ∧ p.editMode = .vi ∧ p.bellStyle = .visual ∧ p.maxHistorySize = some 500 ∧
    p.historyDuplicates = .ignoreConsecutive ∧ p.completionType = .menu ∧ p.completionPaging = false ∧
    p.completionPromptLimit = none ∧ p.listCompletionsImmediately = false ∧
    p.customBindings = [(Key.ctrl 't', [.plain .up])] ∧ p.historySuggestions = true ∧
    p.prefixHistorySearch = true ∧ p.keySeqTimeout = 30 ∧
    -- key sequences apply to the named terminal only (or to all when unnamed)
    p.keySeqTable (some "xterm") =
      [([0x1B, 0x5B, 0x31, 0x3B, 0x35, 0x44], ⟨.left, { ctrl := true }⟩), ([0x1B, 0x5B, 0x39, 0x39, 0x7E], .plain (.fn 12))] ∧
    p.keySeqTable (some "rxvt") = [([0x1B, 0x5B, 0x39, 0x39, 0x7E], .plain (.fn 12))] := by
  decide +kernel

example : (Prefs.parse "viCursorShape: False").1.viCursorShape = false := by decide +kernel

/-- Defaults match Haskeline's. -/
example : (Prefs.parse "").1.maxHistorySize = some 100 := by decide +kernel
example : (Prefs.parse "").1.editMode = .emacs := by decide +kernel
example : (Prefs.parse "").1.completionPromptLimit = some 100 := by decide +kernel

/-- Problems are reported, with line numbers, instead of being ignored. -/
example : (Prefs.parse "editMode: Vim\nfoo: 1\nnonsense\nbellStyle: NoBell").2 =
    ["line 1: invalid value for editMode: Vim", "line 2: unknown preference: foo",
     "line 3: expected 'field: value'"] := by decide +kernel
/-- …and the valid lines still apply. -/
example : (Prefs.parse "editMode: Vim\nbellStyle: NoBell").1.bellStyle = .none := by decide +kernel
/-- Field names are case-insensitive and values accept plain spellings. -/
example : (Prefs.parse "EDITMODE: vi\nmax-history-size: 7").1.maxHistorySize = some 7 := by decide +kernel
example : (Prefs.parse "maxhistorysize: unlimited").1.maxHistorySize = none := by decide +kernel

/-! ## Quoted strings -/

example : Prefs.parseQuoted "\"\\ESC[A\" up" = some ([0x1B, 0x5B, 0x41], " up") := by decide +kernel
example : Prefs.parseQuoted "\"\\27[B\"" = some ([0x1B, 0x5B, 0x42], "") := by decide +kernel
example : Prefs.parseQuoted "\"\\x1bOP\"" = some ([0x1B, 0x4F, 0x50], "") := by decide +kernel
example : Prefs.parseQuoted "\"é\"" = some ([0xC3, 0xA9], "") := by decide +kernel
example : Prefs.parseQuoted "\"unterminated" = none := by decide +kernel

/-! ## Key names -/

example : Key.parse? "ctrl-a" = some (Key.ctrl 'a') := by decide +kernel
example : Key.parse? "C-a" = some (Key.ctrl 'a') := by decide +kernel
example : Key.parse? "meta-f" = some (Key.alt 'f') := by decide +kernel
example : Key.parse? "M-f" = some (Key.alt 'f') := by decide +kernel
example : Key.parse? "C-M-Left" = some ⟨.left, { ctrl := true, alt := true }⟩ := by decide +kernel
example : Key.parse? "shift-tab" = some ⟨.tab, { shift := true }⟩ := by decide +kernel
example : Key.parse? "F11" = some (.plain (.fn 11)) := by decide +kernel
example : Key.parse? "PageDown" = some (.plain .pageDown) := by decide +kernel
example : Key.parse? "space" = some (Key.char ' ') := by decide +kernel
example : Key.parse? "A" = some (Key.char 'A') := by decide +kernel
example : Key.parse? "nonsense" = none := by decide +kernel
/-- Aliases a terminal cannot distinguish are normalised. -/
example : Key.parse? "ctrl-i" = some (.plain .tab) := by decide +kernel
example : Key.parse? "C-m" = some (.plain .enter) := by decide +kernel
example : Key.parse? "ctrl-[" = some (.plain .escape) := by decide +kernel
example : Key.parseSeq? "C-x C-e" = some [Key.ctrl 'x', Key.ctrl 'e'] := by decide +kernel
example : Key.parseSeq? "C-x bogus" = none := by decide +kernel

/-- Printing and parsing key names agree. -/
theorem parse_toString : ∀ k ∈ [Key.ctrl 'a', Key.alt 'f', Key.char 'x', .plain .left, .plain (.fn 7),
    ⟨.left, { ctrl := true, alt := true }⟩, ⟨.tab, { shift := true }⟩, .plain .backspace, .plain .enter,
    .plain .escape, Key.char ' ', ⟨.delete, { alt := true }⟩, .plain .pageUp, .plain .home],
    Key.parse? (toString k) = some k := by
  decide +kernel

example : toString (Key.ctrl 'x') = "C-x" := by decide +kernel
example : toString (⟨.right, { ctrl := true, alt := true }⟩ : Key) = "C-M-Right" := by decide +kernel

end Leanline.Tests
