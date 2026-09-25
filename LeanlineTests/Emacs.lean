import LeanlineTests.Support
import LeanlineTests.LineBuffer

/-!
# Theorems: Emacs mode

Every example runs the pure editor on a key sequence and is checked by
evaluation in the kernel. The general theorems at the end hold for every
editor state.
-/

namespace Leanline.Tests

open Editor

/-! ## Insertion and movement -/

example : text (run emacs [] (typeKeys "hello")) = "hello" := by decide +kernel
example : cursor (run emacs [] (typeKeys "hello")) = 5 := by decide +kernel
example : text (run emacs [] (typeKeys "hello" ++ [Key.ctrl 'a'] ++ typeKeys ">")) = ">hello" := by decide +kernel
example : text (run emacs [] (typeKeys "helo" ++ [Key.ctrl 'b'] ++ typeKeys "l")) = "hello" := by decide +kernel
example : cursor (run emacs [] (typeKeys "hello" ++ [Key.ctrl 'a', Key.ctrl 'f', Key.ctrl 'f', Key.ctrl 'e'])) = 5 := by
  decide +kernel
example : cursor (run emacs [] (typeKeys "foo bar baz" ++ [Key.ctrl 'a', Key.alt 'f'])) = 3 := by decide +kernel
example : cursor (run emacs [] (typeKeys "foo bar baz" ++ [Key.ctrl 'a', Key.alt 'f', Key.alt 'f'])) = 7 := by
  decide +kernel
example : cursor (run emacs [] (typeKeys "foo bar baz" ++ [Key.alt 'b'])) = 8 := by decide +kernel
example : cursor (run emacs [] (typeKeys "foo bar" ++ [⟨.left, { ctrl := true }⟩])) = 4 := by decide +kernel
example : cursor (run emacs [] (typeKeys "abc" ++ [.plain .home])) = 0 := by decide +kernel
/-- Combining marks attach to the previous character: one cursor step skips both. -/
example : cursor (run emacs [] (typeKeys "éx" ++ [left, left])) = 0 := by decide +kernel
example : text (run emacs [] (typeKeys "é" ++ [bs])) = "" := by decide +kernel

/-! ## Deletion, killing, yanking -/

example : text (run emacs [] (typeKeys "hello" ++ [bs])) = "hell" := by decide +kernel
example : text (run emacs [] (typeKeys "hello" ++ [Key.ctrl 'a', Key.ctrl 'd'])) = "ello" := by decide +kernel
example : text (run emacs [] (typeKeys "hello" ++ [Key.ctrl 'a', .plain .delete])) = "ello" := by decide +kernel
/-- Backspace at the start of the line rings the bell. -/
example : (run emacs [] [bs]).effects = [.bell] := by decide +kernel
example : text (run emacs [] (typeKeys "hello world" ++ [Key.ctrl 'w'])) = "hello " := by decide +kernel
example : text (run emacs [] (typeKeys "hello world" ++ [Key.alt 'b', Key.ctrl 'k'])) = "hello " := by decide +kernel
example : text (run emacs [] (typeKeys "hello world" ++ [Key.alt 'b', Key.ctrl 'u'])) = "world" := by decide +kernel
example : text (run emacs [] (typeKeys "hello world" ++ [Key.ctrl 'a', Key.alt 'd'])) = " world" := by decide +kernel
example : text (run emacs [] (typeKeys "foo.bar" ++ [⟨.backspace, { alt := true }⟩])) = "foo." := by decide +kernel
/-- `C-w` kills to the previous whitespace; `M-Backspace` to the previous word boundary. -/
example : text (run emacs [] (typeKeys "cd foo/bar" ++ [Key.ctrl 'w'])) = "cd " := by decide +kernel
example : text (run emacs [] (typeKeys "hello world" ++ [Key.ctrl 'a', Key.alt 'd', Key.ctrl 'e', Key.ctrl 'y'])) =
    " worldhello" := by decide +kernel
/-- Consecutive kills accumulate into one kill-ring entry. -/
example : text (run emacs [] (typeKeys "a b c" ++ [Key.ctrl 'w', Key.ctrl 'w', Key.ctrl 'e', Key.ctrl 'y'])) =
    "a b c" := by decide +kernel
example : (run emacs [] (typeKeys "a b c" ++ [Key.ctrl 'w', Key.ctrl 'w'])).state.kill.entries = [graphemesOf "b c"] := by
  decide +kernel
/-- `M-y` after `C-y` replaces the yanked text with the previous kill. -/
example : text (run emacs [] (typeKeys "one two" ++ [Key.ctrl 'w', Key.ctrl 'b', Key.ctrl 'w', Key.ctrl 'e',
    Key.ctrl 'y', Key.alt 'y'])) = " two" := by decide +kernel
example : (run emacs [] (typeKeys "x" ++ [Key.alt 'y'])).effects = [.bell] := by decide +kernel
example : text (run emacs [] (typeKeys "hello world" ++ [Key.ctrl 'x', bs])) = "" := by decide +kernel

/-! ## Transformations -/

example : text (run emacs [] (typeKeys "ab" ++ [Key.ctrl 't'])) = "ba" := by decide +kernel
example : text (run emacs [] (typeKeys "abc" ++ [Key.ctrl 'a', Key.ctrl 'f', Key.ctrl 't'])) = "bac" := by
  decide +kernel
example : text (run emacs [] (typeKeys "hello world" ++ [Key.ctrl 'a', Key.alt 'u'])) = "HELLO world" := by
  decide +kernel
example : text (run emacs [] (typeKeys "HELLO WORLD" ++ [Key.ctrl 'a', Key.alt 'l', Key.alt 'c'])) = "hello World" := by
  decide +kernel
example : text (run emacs [] (typeKeys "élan" ++ [Key.ctrl 'a', Key.alt 'u'])) = "ÉLAN" := by decide +kernel

/-! ## Numeric arguments and quoting -/

example : text (run emacs [] ([Key.alt '3'] ++ typeKeys "x")) = "xxx" := by decide +kernel
example : text (run emacs [] ([Key.alt '1', Key.alt '2'] ++ typeKeys "-")) = "------------" := by decide +kernel
example : text (run emacs [] (typeKeys "abcdef" ++ [Key.alt '3', Key.ctrl 'b', Key.ctrl 'k'])) = "abc" := by
  decide +kernel
example : text (run emacs [] [Key.ctrl 'v', Key.ctrl 'a']) = "\x01" := by decide +kernel
example : text (run emacs [] [Key.ctrl 'v', tab]) = "\t" := by decide +kernel

/-! ## Undo -/

/-- A run of typed characters is undone in one step. -/
example : text (run emacs [] (typeKeys "hello world" ++ [Key.ctrl '_'])) = "" := by decide +kernel
example : text (run emacs [] (typeKeys "hello world" ++ [Key.ctrl 'w', Key.ctrl '_'])) = "hello world" := by
  decide +kernel
example : text (run emacs [] (typeKeys "ab" ++ [Key.ctrl 'a'] ++ typeKeys "x" ++ [Key.ctrl '_'])) = "ab" := by
  decide +kernel
example : text (run emacs [] (typeKeys "ab" ++ [Key.ctrl 'w', Key.ctrl 'x', Key.ctrl 'u'])) = "ab" := by decide +kernel
example : (run emacs [] [Key.ctrl '_']).effects = [.bell] := by decide +kernel
/-- `M-r` reverts all changes to the line. -/
example : text (Editor.handleKeys emacs (Editor.initial emacs [] {} (LineBuffer.ofString "draft"))
    (typeKeys " one" ++ [Key.ctrl 'w', Key.ctrl 'w', Key.alt 'r'])) = "draft" := by decide +kernel

/-! ## History -/

def hist : List String := ["newest", "middle", "oldest"]

example : text (run emacs hist [up]) = "newest" := by decide +kernel
example : text (run emacs hist [up, up]) = "middle" := by decide +kernel
example : text (run emacs hist [up, up, up, up]) = "oldest" := by decide +kernel
example : (run emacs hist [up, up, up, up]).effects = [.bell] := by decide +kernel
example : text (run emacs hist (typeKeys "draft" ++ [up, up, down, down])) = "draft" := by decide +kernel
example : text (run emacs hist [Key.alt '<']) = "oldest" := by decide +kernel
example : text (run emacs hist (typeKeys "x" ++ [Key.alt '<', Key.alt '>'])) = "x" := by decide +kernel
/-- Edits to a recalled entry are kept while moving through the history. -/
example : text (run emacs hist ([up] ++ typeKeys "!" ++ [down, up])) = "newest!" := by decide +kernel
/-- …but the stored history is not modified. -/
example : (run emacs hist ([up] ++ typeKeys "!" ++ [down])).state.history = hist := by decide +kernel

def gitHist : List String := ["git push", "ls -l", "git commit", "make"]

/-- `M-p` finds entries starting with the text before the cursor. -/
example : text (run emacs gitHist (typeKeys "git" ++ [Key.alt 'p'])) = "git push" := by decide +kernel
example : text (run emacs gitHist (typeKeys "git" ++ [Key.alt 'p', Key.alt 'p'])) = "git commit" := by decide +kernel
example : text (run emacs gitHist (typeKeys "git" ++ [Key.alt 'p', Key.alt 'p', Key.alt 'n'])) = "git push" := by
  decide +kernel
example : text (run emacs gitHist (typeKeys "git" ++ [Key.alt 'p', Key.alt 'n'])) = "git" := by decide +kernel
/-- With `prefixHistorySearch`, the arrow keys search by prefix. -/
example : text (run { prefixHistorySearch := true } gitHist (typeKeys "m" ++ [up])) = "make" := by decide +kernel
example : text (run { prefixHistorySearch := true } gitHist [up, up]) = "ls -l" := by decide +kernel

/-- Incremental search with `C-r`. -/
example : text (run emacs gitHist ([Key.ctrl 'r'] ++ typeKeys "comm")) = "git commit" := by decide +kernel
example : cursor (run emacs gitHist ([Key.ctrl 'r'] ++ typeKeys "comm")) = 4 := by decide +kernel
example : text (run emacs gitHist ([Key.ctrl 'r'] ++ typeKeys "git" ++ [Key.ctrl 'r'])) = "git commit" := by
  decide +kernel
example : (run emacs gitHist ([Key.ctrl 'r'] ++ typeKeys "comm" ++ [enter])).status = .accept "git commit" := by
  decide +kernel
/-- `C-g` abandons the search and restores the line. -/
example : text (run emacs gitHist (typeKeys "draft" ++ [Key.ctrl 'r'] ++ typeKeys "ls" ++ [Key.ctrl 'g'])) =
    "draft" := by decide +kernel
/-- Any other key accepts the match and then acts normally. -/
example : text (run emacs gitHist ([Key.ctrl 'r'] ++ typeKeys "ls" ++ [Key.ctrl 'e'] ++ typeKeys "a")) = "ls -la" := by
  decide +kernel
/-- A failing search is reported in the prompt and with the bell. -/
example : (Editor.view emacs (run emacs gitHist ([Key.ctrl 'r'] ++ typeKeys "zzz")).state).prompt =
    some "(failed reverse-i-search)`zzz': " := by decide +kernel
/-- Backspace in the search shortens the query. -/
example : text (run emacs gitHist ([Key.ctrl 'r'] ++ typeKeys "lsx" ++ [bs])) = "ls -l" := by decide +kernel
/-- Enter accepts the entry found. -/
example : text (run emacs gitHist ([Key.ctrl 'r'] ++ typeKeys "make" ++ [enter])) = "make" := by decide +kernel

/-- `M-.` inserts the last word of the previous command; repeating goes further back. -/
example : text (run emacs ["cp a.txt b.txt", "ls docs"] (typeKeys "cd " ++ [Key.alt '.'])) = "cd b.txt" := by
  decide +kernel
example : text (run emacs ["ls docs", "cp a.txt b.txt"] (typeKeys "cd " ++ [Key.alt '.', Key.alt '.'])) =
    "cd b.txt" := by decide +kernel

/-! ## Completion -/

def cmds : List String := ["help", "hello", "history", "quit"]

example : (run emacs [] (typeKeys "he" ++ [tab])).status = .complete .insert := by decide +kernel
/-- A unique candidate is inserted followed by a space. -/
example : text (answer emacs (run emacs [] (typeKeys "q" ++ [tab])) cmds) = "quit " := by decide +kernel
/-- Several candidates: their common prefix is inserted. -/
example : text (answer emacs (run emacs [] (typeKeys "h" ++ [tab])) ["help", "hello"]) = "hel" := by decide +kernel
/-- No progress possible: the candidates are listed. -/
example : (answer emacs (run emacs [] (typeKeys "hel" ++ [tab])) cmds).effects = [.listCompletions ["help", "hello"]] := by
  decide +kernel
/-- Without `listCompletionsImmediately` the first Tab rings, the second lists. -/
example : (answer { listCompletionsImmediately := false } (run { listCompletionsImmediately := false } []
    (typeKeys "hel" ++ [tab])) cmds).effects = [.bell] := by decide +kernel
example :
    let cfg : EditorConfig := { listCompletionsImmediately := false }
    let r1 := answer cfg (run cfg [] (typeKeys "hel" ++ [tab])) cmds
    (answer cfg (cont cfg r1 [tab]) cmds).effects = [.listCompletions ["help", "hello"]] := by decide +kernel
example : (answer emacs (run emacs [] (typeKeys "xyz" ++ [tab])) cmds).effects = [.bell] := by decide +kernel
/-- Completion keeps the text after the cursor. -/
example : text (answer emacs (run emacs [] (typeKeys "q rest" ++ [Key.alt 'b', Key.ctrl 'b', tab])) cmds) =
    "quit  rest" := by decide +kernel
/-- Completion can be undone. -/
example : text (cont emacs (answer emacs (run emacs [] (typeKeys "q" ++ [tab])) cmds) [Key.ctrl '_']) = "q" := by
  decide +kernel

/-- Menu completion cycles through the candidates and back to the original. -/
def menu : EditorConfig := { completionType := .menu }
example : text (answer menu (run menu [] (typeKeys "he" ++ [tab])) cmds) = "help" := by decide +kernel
example : text (cont menu (answer menu (run menu [] (typeKeys "he" ++ [tab])) cmds) [tab]) = "hello" := by
  decide +kernel
example : text (cont menu (answer menu (run menu [] (typeKeys "he" ++ [tab])) cmds) [tab, tab]) = "he" := by
  decide +kernel
example : text (cont menu (answer menu (run menu [] (typeKeys "he" ++ [tab])) cmds) [⟨.tab, { shift := true }⟩]) =
    "he" := by decide +kernel
/-- Any other key keeps the current candidate and acts normally. -/
example : text (cont menu (answer menu (run menu [] (typeKeys "he" ++ [tab])) cmds) [tab] |> (cont menu · (typeKeys "!"))) =
    "hello!" := by decide +kernel

/-! ## Finishing -/

example : (run emacs [] (typeKeys "ls" ++ [enter])).status = .accept "ls" := by decide +kernel
example : (run emacs [] (typeKeys "ls" ++ [Key.ctrl 'j'])).status = .accept "ls" := by decide +kernel
example : (run emacs [] (typeKeys "ls" ++ [Key.ctrl 'a', enter])).status = .accept "ls" := by decide +kernel
example : (run emacs [] [Key.ctrl 'd']).status = .eof := by decide +kernel
example : (run emacs [] (typeKeys "x" ++ [Key.ctrl 'd'])).status = .editing := by decide +kernel
example : (run emacs [] (typeKeys "x" ++ [Key.ctrl 'c'])).status = .interrupt := by decide +kernel
example : (run emacs [] [Key.ctrl 'l']).effects = [.clearScreen] := by decide +kernel
example : (run emacs [] [Key.ctrl 'z']).effects = [.suspend] := by decide +kernel
example : (run emacs [] [Key.ctrl 'x', Key.ctrl 'e']).effects = [.editInEditor] := by decide +kernel
/-- Keys after the line is finished are not processed. -/
example : (run emacs [] (typeKeys "a" ++ [enter] ++ typeKeys "b")).status = .accept "a" := by decide +kernel

/-! ## Multi-line input -/

def parens : EditorConfig :=
  { isComplete := fun s => decide (s.toList.count '(' ≤ s.toList.count ')') }

/-- Enter continues an incomplete input on a new line… -/
example : (run parens [] (typeKeys "(a" ++ [enter])).status = .editing := by decide +kernel
/-- …and accepts it once complete. -/
example : (run parens [] (typeKeys "(a" ++ [enter] ++ typeKeys "b)" ++ [enter])).status = .accept "(a\nb)" := by
  decide +kernel
/-- `M-Enter` always inserts a line break. -/
example : text (run emacs [] (typeKeys "a" ++ [⟨.enter, { alt := true }⟩] ++ typeKeys "b")) = "a\nb" := by
  decide +kernel
/-- Up and Down move between the lines of a multi-line input before touching history. -/
example : cursor (run parens hist (typeKeys "(abc" ++ [enter] ++ typeKeys "d" ++ [up])) = 1 := by decide +kernel
example : text (run parens hist (typeKeys "(abc" ++ [enter] ++ typeKeys "d" ++ [up, up])) = "newest" := by
  decide +kernel
example : cursor (run parens hist (typeKeys "(abc" ++ [enter] ++ typeKeys "d" ++ [up, Key.ctrl 'a', down])) = 5 := by
  decide +kernel

/-! ## Pasting -/

/-- Pasted text is inserted verbatim: its line break does not accept the line. -/
example : let r := Editor.handleEvent emacs (Editor.initial emacs []) (.paste "echo 1\necho 2")
    text r = "echo 1\necho 2" ∧ r.status = .editing := by decide +kernel

/-! ## Suggestions -/

def suggest : EditorConfig := { suggestions := true }

example : (Editor.view suggest (run suggest ["git status"] (typeKeys "git s")).state).hint = graphemesOf "tatus" := by
  decide +kernel
example : text (run suggest ["git status"] (typeKeys "git s" ++ [Key.ctrl 'e'])) = "git status" := by decide +kernel
example : text (run suggest ["git status"] (typeKeys "git s" ++ [right])) = "git status" := by decide +kernel
/-- No suggestion unless the cursor is at the end. -/
example : (Editor.view suggest (run suggest ["git status"] (typeKeys "git s" ++ [left])).state).hint = [] := by
  decide +kernel
example : (Editor.view emacs (run emacs ["git status"] (typeKeys "git s")).state).hint = [] := by decide +kernel

/-! ## Custom bindings -/

/-- Program-defined bindings take precedence over the built-in keymap. -/
example : text (run { bindings := [([Key.ctrl 't'], .insertText "<now>")] } [] (typeKeys "a" ++ [Key.ctrl 't'])) =
    "a<now>" := by decide +kernel
/-- Multi-key bindings. -/
example : text (run { bindings := [([Key.ctrl 'c', Key.char 'd'], .insertText "done")] } [] [Key.ctrl 'c', Key.char 'd']) =
    "done" := by decide +kernel
example : (run { bindings := [([Key.ctrl 'c', Key.char 'd'], .noop)] } [] [Key.ctrl 'c']).state.pending = [Key.ctrl 'c'] := by
  decide +kernel
/-- Macros (the preferences file's `bind:`) replay other keys. -/
example : text (run { macros := [(Key.ctrl 't', [Key.ctrl 'a', Key.char '#'])] } [] (typeKeys "ls" ++ [Key.ctrl 't'])) =
    "#ls" := by decide +kernel

/-! ## Passwords -/

def pw : EditorConfig := { password := true }

example : text (run pw hist (typeKeys "s3cret" ++ [up])) = "s3cret" := by decide +kernel
example : (run pw hist [Key.ctrl 'r']).effects = [.bell] := by decide +kernel
example : (run pw [] [tab]).effects = [.bell] := by decide +kernel
/-- Killed password text never reaches the kill ring. -/
example : (run pw [] (typeKeys "s3cret" ++ [Key.ctrl 'u'])).state.kill.entries = [] := by decide +kernel

/-! ## General theorems -/

/-- Book-keeping for undo never changes the buffer or the outcome. -/
theorem recordUndo_buf (cmd : Command) (s : EditorState) (r : StepResult) :
    (recordUndo cmd s r).state.buf = r.state.buf ∧ (recordUndo cmd s r).status = r.status ∧
    (recordUndo cmd s r).effects = r.effects :=
  ⟨rfl, rfl, rfl⟩

/-- No printable ASCII key is bound in the Emacs keymap: they all self-insert. -/
theorem emacs_printable_unbound :
    ∀ i : Fin 95, Keymaps.emacs.lookup [Key.char (Char.ofNat (i.val + 32))] = .unbound := by
  decide +kernel

theorem printable_char (i : Fin 95) :
    (Key.char (Char.ofNat (i.val + 32))).printable? = some (Char.ofNat (i.val + 32)) := by
  revert i; decide +kernel

/-- The printable ASCII character number `i` (from space to `~`). -/
def ch (i : Fin 95) : Char := Char.ofNat (i.val + 32)

/-- An Emacs-mode state waiting for an ordinary key. -/
structure Ready (s : EditorState) : Prop where
  mode : s.mode = .emacs
  overlay : s.overlay = .none
  pending : s.pending = []
  arg : s.arg = none

theorem recordInsert_fields (f : List Grapheme → List Grapheme) (st : EditorState) :
    (recordInsert f st).buf = st.buf ∧ (recordInsert f st).mode = st.mode ∧
    (recordInsert f st).overlay = st.overlay ∧ (recordInsert f st).pending = st.pending ∧
    (recordInsert f st).arg = st.arg := by
  unfold recordInsert; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- From any Emacs-mode state without a pending key sequence, argument or
overlay, typing a printable ASCII character inserts exactly that character at
the cursor, and the editor is ready for the next key. -/
theorem emacs_selfInsert (i : Fin 95) (s : EditorState) (cfg : EditorConfig) (h : Ready s)
    (hbind : cfg.bindings = []) :
    let r := handleKey cfg s (Key.char (ch i))
    r.status = .editing ∧ r.state.buf = s.buf.insertChar (ch i) ∧ Ready r.state := by
  have hl := emacs_printable_unbound i
  have hp := printable_char i
  have hb : cfg.bindings.lookup [Key.char (ch i)] = .unbound := by simp [hbind, Keymap.lookup]
  obtain ⟨hmode, hov, hpend, harg⟩ := h
  simp only [ch] at *
  simp only [handleKey, hov, dispatch, hmode, keymapKey, hpend, List.nil_append, lookupKeys, hb, hl,
    List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp, runCommand, recordUndo]
  simp only [exec, harg, hp, hmode]
  obtain ⟨h1, h2, h3, h4, h5⟩ := recordInsert_fields
    (fun x => x ++ List.replicate 1 (Grapheme.ofChar (Char.ofNat (i.val + 32))))
    { s with arg := none, pending := [], last := .insert,
             buf := LineBuffer.iterate 1 (fun x => LineBuffer.insertChar (Char.ofNat (i.val + 32)) x) s.buf }
  simp only [Option.getD_none] at *
  refine ⟨rfl, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;> simp_all [ok, LineBuffer.iterate]

theorem insertChar_after (b : LineBuffer) (c : Char) : (b.insertChar c).after = b.after := by
  unfold LineBuffer.insertChar
  split
  · split <;> rfl
  · rfl

theorem chars_of_atEnd (b : LineBuffer) (h : b.after = []) (c : Char) :
    (b.insertChar c).chars = b.chars ++ [c] := by
  rw [Tests.chars_insertChar]
  simp [LineBuffer.chars, LineBuffer.graphemes, h, charsOf]

/-- Typing any sequence of printable ASCII characters appends exactly those
characters to the line. -/
theorem type_ascii (cs : List (Fin 95)) (r : StepResult) (h : Ready r.state)
    (hst : r.status = .editing) (hend : r.state.buf.after = []) :
    (feed emacs r (cs.map fun i => Key.char (ch i))).state.buf.chars = r.state.buf.chars ++ cs.map ch := by
  induction cs generalizing r with
  | nil => simp [feed]
  | cons i is ih =>
    obtain ⟨hs, hbuf, hready⟩ := emacs_selfInsert i r.state emacs h rfl
    have hev : Editor.handleEvent emacs r.state (.key (Key.char (ch i))) = handleKey emacs r.state (Key.char (ch i)) := rfl
    simp only [List.map_cons, feed, hev, hs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    let r' := handleKey emacs r.state (Key.char (ch i))
    rw [ih { state := r'.state, effects := r.effects ++ r'.effects } hready rfl
      (by simp [r', hbuf, insertChar_after, hend])]
    simp [r', hbuf, chars_of_atEnd _ hend]

/-- In particular, typing into an empty editor yields exactly the typed text. -/
theorem type_ascii_fresh (cs : List (Fin 95)) :
    (run emacs [] (cs.map fun i => Key.char (ch i))).state.buf.chars = cs.map ch := by
  have := type_ascii cs { state := Editor.initial emacs [] } ⟨rfl, rfl, rfl, rfl⟩ rfl rfl
  simpa [run, LineBuffer.chars, Editor.initial, emacs, charsOf] using this

end Leanline.Tests
