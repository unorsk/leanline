import Leanline.Grapheme

/-!
# Rendering

Pure layout of the prompt and line on a terminal of a given width, producing
the exact bytes to send. The line is redrawn from the prompt's first row on
every change: move to the start, clear to the end of the screen, write the
content with explicit line breaks at wrap points, then move the cursor into
place. Explicit breaks make the result independent of how a terminal handles
the last column, and wide characters that do not fit on a row are moved to
the next one the same way terminals do.

Prompts may contain ANSI escape sequences (colours, OSC hyperlinks); they
occupy no columns.
-/

namespace Leanline.Render

/-- A unit of output. -/
inductive Cell where
  /-- Text occupying `width` columns (0 for escape sequences and marks). -/
  | text (s : String) (width : Nat)
  | newline
  | tab
  deriving DecidableEq, Repr, Inhabited

/-- Position on screen relative to the first row of the prompt. `col` may
equal the terminal width: the cursor then waits at the right margin. -/
structure Pos where
  row : Nat := 0
  col : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def tabStop : Nat := 8

/-- Output for one cell and the position after it. Lines wrap softly: the
terminal moves text that does not fit to the next row by itself (including
a wide character that would straddle the margin), so that terminals which
reflow text on resize can rejoin the rows. -/
def advance (width : Nat) (p : Pos) : Cell → String × Pos
  | .text s w =>
    if w == 0 then (s, p)
    else if p.col + w > width then (s, { row := p.row + 1, col := w })
    else (s, { p with col := p.col + w })
  | .newline => ("\r\n", { row := p.row + 1, col := 0 })
  | .tab =>
    let p' : Pos := if p.col ≥ width then { row := p.row + 1, col := 0 } else p
    let n := min (tabStop - p'.col % tabStop) (width - p'.col)
    (String.ofList (List.replicate n ' '), { p' with col := p'.col + n })

/-- Lay out cells from `start`, returning the output and the final position. -/
def layout (width : Nat) (start : Pos) (cells : List Cell) : String × Pos :=
  cells.foldl (fun (out, p) c => let (s, p') := advance width p c; (out ++ s, p')) ("", start)

/-- Where the terminal cursor really is: a position at the right margin is
shown at the start of the next row. -/
def normalize (width : Nat) (p : Pos) : Pos :=
  if p.col ≥ width then { row := p.row + 1, col := 0 } else p

/-! ## Styles

Syntax highlighting is expressed as styles attached to character ranges of
the line. A highlighter cannot change the text itself, so it can never make
the display disagree with the buffer. -/

inductive Color where
  | black | red | green | yellow | blue | magenta | cyan | white
  | brightBlack | brightRed | brightGreen | brightYellow
  | brightBlue | brightMagenta | brightCyan | brightWhite
  /-- An entry of the 256-colour palette. -/
  | palette (n : UInt8)
  | rgb (r g b : UInt8)
  deriving DecidableEq, Repr, Inhabited

structure Style where
  fg : Option Color := none
  bg : Option Color := none
  bold : Bool := false
  dim : Bool := false
  italic : Bool := false
  underline : Bool := false
  reverse : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A style for the characters `[start, stop)` of the line (character
offsets). Later spans take precedence over earlier ones. -/
structure Span where
  start : Nat
  stop : Nat
  style : Style
  deriving DecidableEq, Repr, Inhabited

def Color.sgr (background : Bool) : Color → String
  | .palette n => (if background then "48;5;" else "38;5;") ++ toString n.toNat
  | .rgb r g b => (if background then "48;2;" else "38;2;") ++ s!"{r.toNat};{g.toNat};{b.toNat}"
  | c =>
    let idx := match c with
      | .black => 0 | .red => 1 | .green => 2 | .yellow => 3
      | .blue => 4 | .magenta => 5 | .cyan => 6 | .white => 7
      | .brightBlack => 60 | .brightRed => 61 | .brightGreen => 62 | .brightYellow => 63
      | .brightBlue => 64 | .brightMagenta => 65 | .brightCyan => 66 | _ => 67
    toString ((if background then 40 else 30) + idx)

/-- The escape sequence selecting `st` (starting from the default style). -/
def Style.sgr (st : Style) : String :=
  let parts := ["0"] ++ (if st.bold then ["1"] else []) ++ (if st.dim then ["2"] else []) ++
    (if st.italic then ["3"] else []) ++ (if st.underline then ["4"] else []) ++
    (if st.reverse then ["7"] else []) ++ (st.fg.map (·.sgr false)).toList ++ (st.bg.map (·.sgr true)).toList
  "\x1b[" ++ ";".intercalate parts ++ "m"

/-- The style of each grapheme, given spans over character offsets. -/
def stylesFor (gs : List Grapheme) (spans : List Span) : List Style :=
  go gs 0
where
  go : List Grapheme → Nat → List Style
    | [], _ => []
    | g :: rest, off =>
      let st := spans.foldl (fun acc sp => if sp.start ≤ off && off < sp.stop then sp.style else acc) {}
      st :: go rest (off + g.toList.length)

/-! ## Cells -/

/-- Split a prompt into cells, treating CSI and OSC escape sequences and the
readline markers `\x01`/`\x02` as zero-width. -/
def promptCells (prompt : String) : List Cell :=
  go prompt.length prompt.toList [] []
where
  flush (pending : List Char) (acc : List Cell) : List Cell :=
    if pending.isEmpty then acc
    else (graphemes pending.reverse).reverse.map (fun g => Cell.text g.toString g.width) ++ acc
  /-- Split an escape sequence (after ESC) from the rest of the input. -/
  escSeq : List Char → List Char × List Char
    | '[' :: rest =>
      let body := rest.takeWhile fun c => !(c.toNat ≥ 0x40 && c.toNat ≤ 0x7E)
      match rest.drop body.length with
      | f :: more => ('[' :: body ++ [f], more)
      | [] => ('[' :: body, [])
    | ']' :: rest =>
      let body := rest.takeWhile fun c => c != '\x07' && c != '\x1b'
      match rest.drop body.length with
      | '\x07' :: more => (']' :: body ++ ['\x07'], more)
      | '\x1b' :: '\\' :: more => (']' :: body ++ ['\x1b', '\\'], more)
      | after => (']' :: body, after)
    | c :: rest => ([c], rest)
    | [] => ([], [])
  -- Every step consumes at least one character, so the length is enough fuel.
  go : Nat → List Char → List Char → List Cell → List Cell
    | 0, _, pending, acc => (flush pending acc).reverse
    | _, [], pending, acc => (flush pending acc).reverse
    | fuel + 1, '\x1b' :: rest, pending, acc =>
      let (sq, more) := escSeq rest
      go fuel more [] (Cell.text (String.ofList ('\x1b' :: sq)) 0 :: flush pending acc)
    | fuel + 1, '\x01' :: rest, pending, acc => go fuel rest pending acc
    | fuel + 1, '\x02' :: rest, pending, acc => go fuel rest pending acc
    | fuel + 1, '\n' :: rest, pending, acc => go fuel rest [] (Cell.newline :: flush pending acc)
    | fuel + 1, c :: rest, pending, acc => go fuel rest (c :: pending) acc

/-- Caret notation for a control character: `^A`, `^?`. -/
def caret (c : Char) : String :=
  if c.toNat == 0x7F then "^?" else "^" ++ (Char.ofNat (c.toNat + 64)).toString

/-- The cell for one grapheme of the edited line. -/
def graphemeCell (g : Grapheme) : Cell :=
  if g.base == '\n' then .newline
  else if g.base == '\t' then .tab
  else if Unicode.isControl g.base then .text (caret g.base) 2
  else .text g.toString g.width

/-- How the line itself is displayed. -/
inductive Echo where
  | plain
  /-- Password entry showing one mask character per grapheme. -/
  | mask (c : Char)
  /-- Password entry showing nothing. -/
  | hidden
  deriving DecidableEq, Repr, Inhabited

def lineCells (echo : Echo) (gs : List Grapheme) : List Cell :=
  match echo with
  | .plain => gs.map graphemeCell
  | .mask c => gs.map fun _ => .text c.toString (Unicode.charWidth c)
  | .hidden => []

/-- Cells for styled graphemes: an escape sequence wherever the style changes,
and a reset at the end. -/
def styledCells (gs : List Grapheme) (styles : List Style) : List Cell :=
  go gs styles {}
where
  go : List Grapheme → List Style → Style → List Cell
    | [], _, cur => if cur == {} then [] else [.text "\x1b[0m" 0]
    | g :: rest, st :: sts, cur =>
      (if st == cur then [] else [.text st.sgr 0]) ++ graphemeCell g :: go rest sts st
    | g :: rest, [], cur =>
      (if cur == {} then [] else [.text "\x1b[0m" 0]) ++ graphemeCell g :: go rest [] {}

def dim : String := "\x1b[2m"
def resetStyle : String := "\x1b[0m"

/-! ## Screen updates -/

/-- Everything needed to draw the prompt line. -/
structure Frame where
  prompt : String
  /-- Graphemes left of the cursor, in order. -/
  before : List Grapheme
  after : List Grapheme
  hint : List Grapheme := []
  echo : Echo := .plain
  /-- Styles for `before.reverse ++ after`, one per grapheme (plain echo only). -/
  styles : List Style := []
  deriving Repr, Inhabited

/-- What is known about the previous drawing. -/
structure Screen where
  /-- Rows from the first row of the prompt down to the cursor. -/
  cursorRow : Nat := 0
  /-- The frame last drawn, used to recompute `cursorRow` after a resize. -/
  frame : Option Frame := none
  deriving Repr, Inhabited

def cursorUp (n : Nat) : String := if n == 0 then "" else s!"\x1b[{n}A"
def cursorRight (n : Nat) : String := if n == 0 then "" else s!"\x1b[{n}C"
def clearToEnd : String := "\x1b[J"
def hideCursor : String := "\x1b[?25l"
def showCursor : String := "\x1b[?25h"

/-- Positions for a frame: where the cursor goes and where output ends. -/
def positions (width : Nat) (f : Frame) : Pos × Pos :=
  let width := max width 1
  let (_, pPrompt) := layout width {} (promptCells f.prompt)
  let (_, pCursor) := layout width pPrompt (lineCells f.echo f.before)
  let (_, pLine) := layout width pCursor (lineCells f.echo f.after)
  let hintCells := if f.hint.isEmpty then [] else lineCells .plain f.hint
  let (_, pEnd) := layout width pLine hintCells
  (normalize width pCursor, normalize width pEnd)

/-- Draw `f`, replacing whatever was drawn before (`prev`). Returns the bytes
to write and the new screen state. -/
def redraw (width : Nat) (prev : Screen) (f : Frame) : String × Screen :=
  let width := max width 1
  let line := f.before ++ f.after
  let lineOut := if f.echo == .plain && !f.styles.isEmpty then styledCells line f.styles
    else lineCells f.echo line
  let cells := promptCells f.prompt ++ lineOut
  let (body, pLine) := layout width {} cells
  let hintCells :=
    if f.hint.isEmpty then [] else [.text dim 0] ++ lineCells .plain f.hint ++ [.text resetStyle 0]
  let (hintOut, pEnd) := layout width pLine hintCells
  let (cur, endPos) := positions width f
  -- At the right margin the terminal holds the cursor on the last column;
  -- a space and a carriage return move it to the start of the next row
  -- without ending the (soft-wrapped) line.
  let wrapFix := if pEnd.col ≥ width then " \r" else ""
  let out := hideCursor ++ cursorUp prev.cursorRow ++ "\r" ++ clearToEnd ++ body ++ hintOut ++ wrapFix ++
    cursorUp (endPos.row - cur.row) ++ "\r" ++ cursorRight cur.col ++ showCursor
  (out, { cursorRow := cur.row, frame := some f })

/-- Adjust to a new terminal width. Terminals that reflow soft-wrapped lines
move the cursor with its text, so the distance from the prompt's first row to
the cursor is recomputed for the new width. -/
def resize (width : Nat) (s : Screen) : Screen :=
  match s.frame with
  | some f => { s with cursorRow := (positions width f).1.row }
  | none => s

/-- Move below the drawn frame (before printing something else or accepting). -/
def moveBelow (width : Nat) (prev : Screen) (f : Frame) : String :=
  let (cur, endPos) := positions width f
  let _ := prev
  let down := endPos.row - cur.row
  (if down == 0 then "" else s!"\x1b[{down}B") ++ "\r\n"

/-! ## Dumb terminals

Terminals without cursor addressing (`TERM=dumb`, such as an Emacs shell
buffer) only get carriage returns and spaces. The line is shown on a single
row that scrolls horizontally to keep the cursor visible, as in Haskeline. -/

/-- Text of a cell on a dumb terminal (escape sequences are dropped). -/
def dumbText : Cell → String × Nat
  | .text s w => if w == 0 then ("", 0) else (s, w)
  | .newline => ("^J", 2)
  | .tab => ("^I", 2)

/-- Draw `f` on one row of a dumb terminal. `prevWidth` is how many columns
the previous drawing used; returns the output and the columns now used. -/
def redrawDumb (width : Nat) (prevWidth : Nat) (f : Frame) : String × Nat :=
  let avail := max (width - 1) 1
  let pieces (cs : List Cell) := (cs.map dumbText).filter (·.2 > 0)
  let promptP := pieces (promptCells f.prompt)
  let beforeP := pieces (lineCells f.echo f.before)
  let afterP := pieces (lineCells f.echo f.after)
  let wOf (ps : List (String × Nat)) := ps.foldl (fun n p => n + p.2) 0
  -- Drop pieces from the left until the cursor fits, then from the right.
  let rec dropLeft (ps : List (String × Nat)) (excess : Nat) : List (String × Nat) :=
    match ps with
    | [] => []
    | p :: rest => if excess == 0 then ps else dropLeft rest (excess - min excess p.2)
  let lead := promptP ++ beforeP
  let lead := if wOf lead ≥ avail then dropLeft lead (wOf lead - avail + 1) else lead
  let rec takeWidth (ps : List (String × Nat)) (budget : Nat) : List (String × Nat) :=
    match ps with
    | [] => []
    | p :: rest => if p.2 ≤ budget then p :: takeWidth rest (budget - p.2) else []
  let trail := takeWidth afterP (avail - wOf lead)
  let text (ps : List (String × Nat)) := String.join (ps.map (·.1))
  let used := wOf lead + wOf trail
  let pad := String.ofList (List.replicate (prevWidth - used) ' ')
  ("\r" ++ text lead ++ text trail ++ pad ++ "\r" ++ text lead, used)

/-! ## Completion listings -/

def displayWidth (s : String) : Nat := widthOf (graphemesOf s)

def padTo (n : Nat) (s : String) : String :=
  s ++ String.ofList (List.replicate (n - displayWidth s) ' ')

/-- Arrange items in columns (filled top to bottom, then left to right) to fit
`width`. Returns one string per row. -/
def columns (width : Nat) (items : List String) : List String :=
  if items.isEmpty then [] else
  let colW := (items.map displayWidth).foldl max 0 + 2
  let ncols := max 1 (width / colW)
  let nrows := (items.length + ncols - 1) / ncols
  (List.range nrows).map fun r =>
    let row := (List.range ncols).filterMap fun c => items[c * nrows + r]?
    match row.reverse with
    | [] => ""
    | lastItem :: revInit => String.join (revInit.reverse.map (padTo colW)) ++ lastItem

end Leanline.Render
