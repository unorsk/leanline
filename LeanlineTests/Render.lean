import Leanline

/-!
# Theorems: rendering

Layout on terminals of a given width: wrapping, wide characters, zero-width
escape sequences in prompts, tabs, line breaks, masking, and the exact bytes
of a redraw.
-/

namespace Leanline.Tests

open Render

def frame (prompt line : String) (cursorAt : Option Nat := none) (echo : Echo := .plain) : Frame :=
  let gs := graphemesOf line
  let n := cursorAt.getD gs.length
  { prompt, before := gs.take n, after := gs.drop n, echo }

/-- Cursor and end position of a frame. -/
def pos (width : Nat) (f : Frame) : (Nat × Nat) × (Nat × Nat) :=
  let (c, e) := positions width f
  ((c.row, c.col), (e.row, e.col))

/-! ## General properties -/

/-- The real cursor is always inside the terminal. -/
theorem normalize_col_lt (width : Nat) (p : Pos) (h : 0 < width) : (normalize width p).col < width := by
  unfold normalize
  split
  · simpa using h
  · omega

theorem normalize_row (width : Nat) (p : Pos) : p.row ≤ (normalize width p).row := by
  unfold normalize; split <;> simp

/-- Text never moves the cursor up. -/
theorem advance_row (width : Nat) (p : Pos) (c : Cell) : p.row ≤ (advance width p c).2.row := by
  cases c <;> simp only [advance] <;> (try split) <;> (try split) <;> simp_all <;> omega

/-- Syntax highlighting assigns exactly one style to every grapheme. -/
theorem stylesFor_length (gs : List Grapheme) (spans : List Span) : (stylesFor gs spans).length = gs.length := by
  unfold stylesFor
  suffices ∀ off, (stylesFor.go spans gs off).length = gs.length from this 0
  induction gs with
  | nil => intro; rfl
  | cons g gs ih => intro off; simp [stylesFor.go, ih]

/-- A masked password shows exactly one mask character per grapheme. -/
theorem lineCells_mask (c : Char) (gs : List Grapheme) : (lineCells (.mask c) gs).length = gs.length := by
  simp [lineCells]

/-- A hidden password shows nothing at all. -/
theorem lineCells_hidden (gs : List Grapheme) : lineCells .hidden gs = [] := rfl

/-! ## Wrapping -/

example : pos 80 (frame "> " "hello") = ((0, 7), (0, 7)) := by decide +kernel
example : pos 80 (frame "> " "hello" (some 0)) = ((0, 2), (0, 7)) := by decide +kernel
/-- Filling a row exactly puts the cursor at the start of the next one. -/
example : pos 20 (frame "λ " "abcdefghijklmnopqr") = ((1, 0), (1, 0)) := by decide +kernel
example : pos 20 (frame "λ " "abcdefghijklmnopqrs") = ((1, 1), (1, 1)) := by decide +kernel
example : pos 10 (frame "" "abcdefghijklmnopqrstuvwxyz" (some 12)) = ((1, 2), (2, 6)) := by decide +kernel
/-- A wide character that does not fit at the end of a row moves to the next row. -/
example : pos 10 (frame "" "abcdefghi日") = ((1, 2), (1, 2)) := by decide +kernel
example : pos 10 (frame "" "abcdefgh日") = ((1, 0), (1, 0)) := by decide +kernel
example : pos 80 (frame "" "日本語") = ((0, 6), (0, 6)) := by decide +kernel
/-- Combining marks take no space. -/
example : pos 80 (frame "" "e\u0301e\u0301") = ((0, 2), (0, 2)) := by decide +kernel
/-- Escape sequences in the prompt take no space. -/
example : pos 80 (frame "\x1b[1;32mλ\x1b[0m " "ab") = ((0, 4), (0, 4)) := by decide +kernel
example : pos 80 (frame "\x1b]8;;http://x\x07link\x1b]8;;\x07> " "") = ((0, 6), (0, 6)) := by decide +kernel
/-- Multi-line prompts and inputs. -/
example : pos 80 (frame "line one\n> " "ab") = ((1, 4), (1, 4)) := by decide +kernel
example : pos 80 (frame "> " "ab\ncd") = ((1, 2), (1, 2)) := by decide +kernel
/-- Tabs advance to the next multiple of eight. -/
example : pos 80 (frame "" "a\tb") = ((0, 9), (0, 9)) := by decide +kernel
/-- Control characters are shown in caret notation, two columns wide. -/
example : pos 80 (frame "" "a\x01b") = ((0, 4), (0, 4)) := by decide +kernel
/-- Passwords. -/
example : pos 80 (frame "pw: " "secret" none (.mask '*')) = ((0, 10), (0, 10)) := by decide +kernel
example : pos 80 (frame "pw: " "secret" none .hidden) = ((0, 4), (0, 4)) := by decide +kernel

/-! ## Output -/

/-- The bytes of a redraw: hide the cursor, return to the prompt's first row,
clear, draw, and move to the cursor. -/
example : (redraw 80 {} (frame "> " "hi")).1 = "\x1b[?25l\r\x1b[J> hi\r\x1b[4C\x1b[?25h" := by decide +kernel
example : (redraw 80 {} (frame "> " "hi" (some 0))).1 = "\x1b[?25l\r\x1b[J> hi\r\x1b[2C\x1b[?25h" := by decide +kernel
/-- Redrawing starts by moving up to the prompt's first row. -/
example : (redraw 10 { cursorRow := 2 } (frame "" "x")).1 = "\x1b[?25l\x1b[2A\r\x1b[Jx\r\x1b[1C\x1b[?25h" := by
  decide +kernel
/-- At the right margin the cursor is moved to the next row explicitly. -/
example : (redraw 4 {} (frame "" "abcd")).1 = "\x1b[?25l\r\x1b[Jabcd \r\r\x1b[?25h" := by decide +kernel
example : (redraw 4 {} (frame "" "abcdef" (some 1))).1 = "\x1b[?25l\r\x1b[Jabcdef\x1b[1A\r\x1b[1C\x1b[?25h" := by
  decide +kernel
example : (redraw 80 {} (frame "" "abcdef" (some 1))).2.cursorRow = 0 := by decide +kernel
/-- History suggestions are drawn dimmed after the line without moving the cursor. -/
example : (redraw 80 {} { frame "> " "gi" with hint := graphemesOf "t status" }).1 =
    "\x1b[?25l\r\x1b[J> gi\x1b[2mt status\x1b[0m\r\x1b[4C\x1b[?25h" := by decide +kernel
/-- Highlighting emits a style change only where the style changes. -/
example : (redraw 80 {} { frame "" "ab c" with
      styles := stylesFor (graphemesOf "ab c") [{ start := 0, stop := 2, style := { fg := some .green, bold := true } }] }).1 =
    "\x1b[?25l\r\x1b[J\x1b[0;1;32mab\x1b[0m c\r\x1b[4C\x1b[?25h" := by decide +kernel
/-- After a resize the cursor row is recomputed for the new width. -/
example : (resize 10 (redraw 40 {} (frame "" "abcdefghijklmnopqrstuvwxyz")).2).cursorRow = 2 := by decide +kernel

/-! ## Dumb terminals -/

example : redrawDumb 20 0 (frame "> " "hello") = ("\r> hello\r> hello", 7) := by decide +kernel
/-- Shorter content blanks out what was there before. -/
example : redrawDumb 20 7 (frame "> " "hi") = ("\r> hi   \r> hi", 4) := by decide +kernel
/-- Long lines scroll horizontally to keep the cursor visible. -/
example : redrawDumb 8 0 (frame "> " "abcdefghij") = ("\refghij\refghij", 6) := by decide +kernel
example : redrawDumb 8 0 (frame "> " "abcdefghij" (some 0)) = ("\r> abcde\r> ", 7) := by decide +kernel

/-! ## Completion listings -/

example : columns 20 ["a", "bb", "ccc"] = ["a    bb   ccc"] := by decide +kernel
example : columns 10 ["alpha", "beta", "gamma"] = ["alpha", "beta", "gamma"] := by decide +kernel
/-- Items fill columns top to bottom. -/
example : columns 12 ["a", "b", "c", "d", "e"] = ["a  c  e", "b  d"] := by decide +kernel
example : columns 80 [] = [] := by decide +kernel

/-! ## Styles -/

example : Style.sgr {} = "\x1b[0m" := by decide +kernel
example : Style.sgr { fg := some (.rgb 255 0 10), underline := true } = "\x1b[0;4;38;2;255;0;10m" := by decide +kernel
example : Style.sgr { bg := some (.palette 236), fg := some .brightCyan } = "\x1b[0;96;48;5;236m" := by decide +kernel

end Leanline.Tests
