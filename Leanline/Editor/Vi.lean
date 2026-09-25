import Leanline.Editor.Core

/-!
# Vi command mode

Command-mode input is parsed into a `ViCommand` by a pure parser over the
keys typed so far (`[count] operator [count] motion`, `[count] command`,
`r<char>`, `f<char>` …) and then executed. The last change is stored as data
so that `.` can replay it, including any text typed in insert mode.
-/

namespace Leanline.Vi

open Editor

inductive Parse where
  | done (c : ViCommand)
  | more
  | invalid
  deriving DecidableEq, Repr

def charOf (k : Key) : Option Char := k.printable?

def digitOf (k : Key) : Option Nat :=
  match charOf k with
  | some c => if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none
  | none => none

/-- Split off a leading count (a `0` on its own is a motion, not a count). -/
def parseCount (ks : List Key) : Option Nat × List Key :=
  match ks with
  | k :: rest =>
    match digitOf k with
    | some d => if d == 0 then (none, ks) else go d rest
    | none => (none, ks)
  | [] => (none, [])
where
  go (acc : Nat) : List Key → Option Nat × List Key
    | k :: rest =>
      match digitOf k with
      | some d => go (acc * 10 + d) rest
      | none => (some acc, k :: rest)
    | [] => (some acc, [])

/-- Motions that take a single key. -/
def simpleMotion (k : Key) : Option ViMotion :=
  match k.base, k.mods == {} with
  | .left, true | .backspace, true => some .left
  | .right, true => some .right
  | .home, true => some .lineStart
  | .end, true => some .lineEnd
  | .char c, true =>
    match c with
    | 'h' => some .left | 'l' | ' ' => some .right
    | 'w' => some (.wordFwd false) | 'W' => some (.wordFwd true)
    | 'b' => some (.wordBack false) | 'B' => some (.wordBack true)
    | 'e' => some (.wordEnd false) | 'E' => some (.wordEnd true)
    | '0' => some .lineStart | '^' => some .firstNonBlank | '$' => some .lineEnd
    | '|' => some .column | '%' => some .matchPair
    | ';' => some (.repeatFind false) | ',' => some (.repeatFind true)
    | _ => none
  | _, _ => none

def findKind (k : Key) : Option (Bool × Bool) :=
  match charOf k with
  | some 'f' => some (true, false)
  | some 'F' => some (false, false)
  | some 't' => some (true, true)
  | some 'T' => some (false, true)
  | _ => none

inductive MotionParse where
  | done (m : ViMotion)
  | more
  | invalid

/-- Parse a motion that must consume exactly `ks`. -/
def parseMotion : List Key → MotionParse
  | [] => .more
  | [k] =>
    match simpleMotion k with
    | some m => .done m
    | none => if (findKind k).isSome then .more else .invalid
  | [k, c] =>
    match findKind k, charOf c with
    | some (fwd, till), some ch => .done (.find (Grapheme.ofChar ch) fwd till)
    | _, _ => .invalid
  | _ => .invalid

def operatorOf (k : Key) : Option ViOperator :=
  match charOf k with
  | some 'd' => some .delete
  | some 'c' => some .change
  | some 'y' => some .yank
  | _ => none

/-- Commands that are not `operator motion`. -/
def simpleCommand (count : Option Nat) (k : Key) (rest : List Key) : Parse :=
  let n := count.getD 1
  let single (c : ViCommand) : Parse := if rest.isEmpty then .done c else .invalid
  if k == Key.ctrl 'r' then single .redo
  else if k == .plain .enter || k == Key.ctrl 'j' then single .accept
  else if k == Key.ctrl 'd' then single .eof
  else if k == Key.ctrl 'c' then single .interrupt
  else if k == Key.ctrl 'l' then single .clearScreen
  else if k == Key.ctrl 'z' then single .suspend
  else if k == Key.ctrl 'p' || k == .plain .up then single (.historyPrev n)
  else if k == Key.ctrl 'n' || k == .plain .down then single (.historyNext n)
  else if k == .plain .delete then single (.deleteChar n)
  else if k == .plain .tab then single .complete
  else if k == .plain .escape then single .cancel
  else match charOf k with
  | some 'i' => single (.insert .here)
  | some 'a' => single (.insert .after)
  | some 'I' => single (.insert .lineStart)
  | some 'A' => single (.insert .lineEnd)
  | some 's' => single (.substitute n)
  | some 'S' => single (.operate .change 1 .wholeLine)
  | some 'C' => single (.operate .change 1 .lineEnd)
  | some 'D' => single (.operate .delete 1 .lineEnd)
  | some 'Y' => single (.operate .yank 1 .wholeLine)
  | some 'x' => single (.deleteChar n)
  | some 'X' => single (.deleteCharBack n)
  | some 'R' => single .replaceMode
  | some '~' => single (.toggleCase n)
  | some 'p' => single (.put n false)
  | some 'P' => single (.put n true)
  | some 'u' => single .undo
  | some 'U' => single .revert
  | some '.' => single (.repeatChange count)
  | some 'k' | some '-' => single (.historyPrev n)
  | some 'j' | some '+' => single (.historyNext n)
  | some 'G' => single .historyOldest
  | some '/' => single (.search true)
  | some '?' => single (.search false)
  | some 'n' => single (.searchAgain false)
  | some 'N' => single (.searchAgain true)
  | some 'v' => single .editInEditor
  | some 'r' =>
    match rest with
    | [] => .more
    | [c] => match charOf c with
      | some ch => .done (.replaceChar n (Grapheme.ofChar ch))
      | none => .invalid
    | _ => .invalid
  | _ =>
    match parseMotion (k :: rest) with
    | .done m => .done (.move n m)
    | .more => .more
    | .invalid => .invalid

/-- Parse the keys typed in command mode so far. -/
def parse (ks : List Key) : Parse :=
  let (c1, rest) := parseCount ks
  match rest with
  | [] => .more
  | k :: rest' =>
    match operatorOf k with
    | some op =>
      let (c2, rest'') := parseCount rest'
      let total := c1.getD 1 * c2.getD 1
      match rest'' with
      | [k2] =>
        if k2 == k then .done (.operate op total .wholeLine)
        else match parseMotion [k2] with
          | .done m => .done (.operate op total m)
          | .more => .more
          | .invalid => .invalid
      | _ =>
        match parseMotion rest'' with
        | .done m => .done (.operate op total m)
        | .more => .more
        | .invalid => .invalid
    | none => simpleCommand c1 k rest'

/-! ## Execution -/

def isOpen (c : Char) : Bool := c == '(' || c == '[' || c == '{'
def isClose (c : Char) : Bool := c == ')' || c == ']' || c == '}'
def partner (c : Char) : Char :=
  match c with
  | '(' => ')' | ')' => '(' | '[' => ']' | ']' => '[' | '{' => '}' | '}' => '{' | _ => c

/-- Position of the bracket matching the first bracket at or after the cursor. -/
def matchPairPos (b : LineBuffer) : Option Nat :=
  let cs := b.graphemes.map (·.base)
  match ((cs.drop b.pos).findIdx? fun c => isOpen c || isClose c) with
  | none => none
  | some off =>
    let i := b.pos + off
    let c := cs[i]?.getD ' '
    if isOpen c then scanFwd c (partner c) (cs.drop (i + 1)) (i + 1) 0
    else scanBack c (partner c) ((cs.take i).reverse) i 0
where
  scanFwd (o cl : Char) : List Char → Nat → Nat → Option Nat
    | [], _, _ => none
    | x :: rest, j, depth =>
      if x == cl then (if depth == 0 then some j else scanFwd o cl rest (j + 1) (depth - 1))
      else if x == o then scanFwd o cl rest (j + 1) (depth + 1)
      else scanFwd o cl rest (j + 1) depth
  scanBack (cl o : Char) : List Char → Nat → Nat → Option Nat
    | [], _, _ => none
    | x :: rest, j, depth =>
      if x == o then (if depth == 0 then some (j - 1) else scanBack cl o rest (j - 1) (depth - 1))
      else if x == cl then scanBack cl o rest (j - 1) (depth + 1)
      else scanBack cl o rest (j - 1) depth

/-- Where a motion leads, and whether an operator should include the target
grapheme. `none` if the motion fails (for example `f` without a match). -/
def motionTarget (s : EditorState) (count : Nat) (m : ViMotion) : Option (Nat × Bool) :=
  let b := s.buf
  let n := max count 1
  match m with
  | .left => some (b.pos - min n b.pos, false)
  | .right => some (min (b.pos + n) b.length, false)
  | .wordFwd big => some ((LineBuffer.iterate n (LineBuffer.viWordForward (cls big)) b).pos, false)
  | .wordBack big => some ((LineBuffer.iterate n (LineBuffer.viWordBackward (cls big)) b).pos, false)
  | .wordEnd big => some ((LineBuffer.iterate n (LineBuffer.viWordEnd (cls big)) b).pos, true)
  | .lineStart => some (0, false)
  | .firstNonBlank => some (b.firstNonBlank.pos, false)
  | .lineEnd => some (b.length, false)
  | .column => some (min (n - 1) b.length, false)
  | .find c fwd till => findTarget b c fwd till n false
  | .repeatFind rev =>
    match s.vi.lastFind with
    | some (c, fwd, till) => findTarget b c (if rev then !fwd else fwd) till n true
    | none => none
  | .matchPair => (matchPairPos b).map (·, true)
  | .wholeLine => some (0, false)
where
  cls (big : Bool) : Grapheme → Nat := if big then LineBuffer.bigClass else LineBuffer.charClass
  /-- When repeating a `t`/`T` search an adjacent match is skipped so that
  the cursor makes progress. -/
  findTarget (b : LineBuffer) (c : Grapheme) (fwd till : Bool) (n : Nat) (skip : Bool) : Option (Nat × Bool) :=
    if fwd then
      match b.findForward c n with
      | some p =>
        if !till then some (p, true)
        else if skip && p - 1 == b.pos then (b.findForward c (n + 1)).map fun q => (q - 1, true)
        else some (p - 1, true)
      | none => none
    else
      match b.findBackward c n with
      | some p =>
        if !till then some (p, false)
        else if skip && p + 1 == b.pos then (b.findBackward c (n + 1)).map fun q => (q + 1, false)
        else some (p + 1, false)
      | none => none

/-- The region an operator acts on. -/
def region (s : EditorState) (target : Nat) (inclusive : Bool) : Nat × Nat :=
  let p := s.buf.pos
  let lo := min p target
  let hi := max p target
  (lo, if inclusive then min (hi + 1) s.buf.length else hi)

def killText (text : List Grapheme) (s : EditorState) : EditorState :=
  { s with kill := s.kill.push text }

def enterInsert (s : EditorState) : EditorState := { s with mode := .vi .insert }

def replaceCount (c : ViCommand) (n : Nat) : ViCommand :=
  match c with
  | .move _ m => .move n m
  | .operate op _ m => .operate op n m
  | .substitute _ => .substitute n
  | .deleteChar _ => .deleteChar n
  | .deleteCharBack _ => .deleteCharBack n
  | .replaceChar _ g => .replaceChar n g
  | .toggleCase _ => .toggleCase n
  | .put _ b => .put n b
  | c => c

/-- Does the command change the line (and so become the target of `.`)? -/
def isChange : ViCommand → Bool
  | .operate op _ _ => op != .yank
  | .insert _ | .substitute _ | .deleteChar _ | .deleteCharBack _ | .replaceChar _ _
  | .replaceMode | .toggleCase _ | .put _ _ => true
  | _ => false

def searchHistory (backward : Bool) (q : List Char) (s : EditorState) : Option EditorState :=
  let current := s.buf.toString
  let p (e : String) := (findSub e.toList q).isSome
  (if backward then s.nav.backUntil p current else s.nav.forwardUntil p current).map fun (e, nav) =>
    { s with buf := (LineBuffer.ofString e).moveToStart, nav }

/-- Execute a vi command (without undo or `.` bookkeeping). -/
def execCommand (cfg : EditorConfig) (cmd : ViCommand) (s : EditorState) : StepResult :=
  let s := { s with pending := [] }
  let clamp (st : EditorState) : EditorState := { st with buf := st.buf.viClamp }
  match cmd with
  | .move n m =>
    match motionTarget s n m with
    | some (p, _) =>
      let s := match m with
        | .find c fwd till => { s with vi := { s.vi with lastFind := some (c, fwd, till) } }
        | _ => s
      ok (clamp { s with buf := s.buf.moveTo p })
    | none => bell s
  | .operate op n m =>
    let m := match op, m, s.buf.after with
      | .change, .wordFwd big, g :: _ => if g.isSpace then m else .wordEnd big
      | _, _, _ => m
    let s := match m with
      | .find c fwd till => { s with vi := { s.vi with lastFind := some (c, fwd, till) } }
      | _ => s
    if m == .wholeLine then
      let text := s.buf.graphemes
      match op with
      | .yank => ok (killText text s)
      | .delete => ok (killText text { s with buf := {} })
      | .change => ok (enterInsert (killText text { s with buf := {} }))
    else match motionTarget s n m with
      | none => bell s
      | some (target, incl) =>
        let (lo, hi) := region s target incl
        let b := s.buf.moveTo lo
        let (b', text) := b.deleteTo hi
        match op with
        | .yank => ok (killText text { s with buf := b.viClamp })
        | .delete => ok (clamp (killText text { s with buf := b' }))
        | .change => ok (enterInsert (killText text { s with buf := b' }))
  | .insert pos =>
    let b := match pos with
      | .here => s.buf
      | .after => s.buf.moveRight
      | .lineStart => s.buf.moveToStart
      | .lineEnd => s.buf.moveToEnd
    ok (enterInsert { s with buf := b })
  | .substitute n =>
    let (b, text) := s.buf.deleteTo (min (s.buf.pos + n) s.buf.length)
    ok (enterInsert (killText text { s with buf := b }))
  | .deleteChar n =>
    if s.buf.atEnd then bell s
    else
      let (b, text) := s.buf.deleteTo (min (s.buf.pos + n) s.buf.length)
      ok (clamp (killText text { s with buf := b }))
  | .deleteCharBack n =>
    if s.buf.atStart then bell s
    else
      let (b, text) := s.buf.deleteTo (s.buf.pos - min n s.buf.pos)
      ok (clamp (killText text { s with buf := b }))
  | .replaceChar n g =>
    let b := s.buf.replaceChars n g
    if b == s.buf && s.buf.after.length < n then bell s else ok { s with buf := b }
  | .replaceMode => ok { s with mode := .vi .replace }
  | .toggleCase n => ok (clamp { s with buf := s.buf.toggleCaseForward n })
  | .put n before =>
    match s.kill.top? with
    | none => bell s
    | some t =>
      let text := (List.replicate n t).flatten
      let b := if before || s.buf.isEmpty then s.buf else s.buf.moveRight
      ok { s with buf := (b.insertList text).moveLeft }
  | .undo => let r := exec cfg .undo (.plain .escape) s; { r with state := clamp r.state }
  | .redo => let r := exec cfg .redo (.plain .escape) s; { r with state := clamp r.state }
  | .revert => ok (clamp { s with buf := s.original })
  | .repeatChange _ => bell s  -- handled by `run`
  | .historyPrev n =>
    if let some b := s.buf.lineUp? then ok (clamp { s with buf := b }) else
    match repeatOpt n histBack s with
    | some s' => ok { s' with buf := s'.buf.moveToStart }
    | none => bell s
  | .historyNext n =>
    if let some b := s.buf.lineDown? then ok (clamp { s with buf := b }) else
    match repeatOpt n histForward s with
    | some s' => ok { s' with buf := s'.buf.moveToStart }
    | none => bell s
  | .historyOldest =>
    let (e, nav) := s.nav.toOldest s.buf.toString
    ok { s with buf := (LineBuffer.ofString e).moveToStart, nav }
  | .search backward =>
    if cfg.password then bell s else ok { s with overlay := .viSearch backward [] s.buf }
  | .searchAgain rev =>
    match s.vi.lastSearch with
    | some (bw, q) =>
      match searchHistory (if rev then !bw else bw) q s with
      | some s' => ok s'
      | none => bell s
    | none => bell s
  | .accept => exec cfg .acceptLine (.plain .enter) s
  | .eof => if s.buf.isEmpty then { state := s, status := .eof } else bell s
  | .interrupt => exec cfg .interrupt (.plain .escape) s
  | .clearScreen => exec cfg .clearScreen (.plain .escape) s
  | .suspend => exec cfg .suspend (.plain .escape) s
  | .editInEditor => exec cfg .editInEditor (.plain .escape) s
  | .complete => exec cfg .complete (.plain .tab) s
  | .cancel => bell s

/-- Commands whose effect on the buffer is not an undoable edit. -/
def notUndoable : ViCommand → Bool
  | .undo | .redo | .historyPrev _ | .historyNext _ | .historyOldest
  | .search _ | .searchAgain _ | .move _ _ | .accept | .eof | .interrupt
  | .clearScreen | .suspend | .cancel | .complete | .editInEditor => true
  | .operate .yank _ _ => true
  | _ => false

/-- Execute a command with undo and `.` bookkeeping. -/
def run (cfg : EditorConfig) (cmd : ViCommand) (s : EditorState) : StepResult :=
  match cmd with
  | .repeatChange count =>
    match s.vi.lastChange with
    | none => bell s
    | some ch =>
      let c := match count with
        | some n => replaceCount ch.cmd n
        | none => ch.cmd
      let r := run' c s
      if r.state.mode == .vi .command then r
      else
        -- Replay the recorded insertion and return to command mode.
        let st := { r.state with buf := r.state.buf.insertList ch.inserted, vi := { r.state.vi with recording := none } }
        let st := enterViCommand st
        { r with state := { st with vi := { st.vi with lastChange := some { ch with cmd := c } } } }
  | _ => run' cmd s
where
  run' (cmd : ViCommand) (s : EditorState) : StepResult :=
    let r := execCommand cfg cmd s
    let st := r.state
    let entered := st.mode != .vi .command
    let st :=
      if notUndoable cmd then st
      else if entered || st.buf.graphemes != s.buf.graphemes then
        { st with undoStack := s.buf :: st.undoStack, redoStack := [], undoGroup := entered }
      else st
    let st :=
      if isChange cmd then
        if entered then { st with vi := { st.vi with recording := some { cmd } } }
        else { st with vi := { st.vi with lastChange := some { cmd } } }
      else st
    { r with state := st }

/-- Handle a key in vi command mode. -/
def commandKey (cfg : EditorConfig) (s : EditorState) (key : Key) : StepResult :=
  let keys := s.pending ++ [key]
  match parse keys with
  | .more => ok { s with pending := keys }
  | .invalid => bell { s with pending := [] }
  | .done cmd => run cfg cmd { s with pending := [] }

/-- Handle a key while typing a `/` or `?` search pattern. -/
def searchKey (s : EditorState) (backward : Bool) (q : List Char) (saved : LineBuffer)
    (key : Key) : StepResult :=
  let cancel := ok { s with overlay := .none, buf := saved }
  if key == .plain .enter || key == Key.ctrl 'j' then
    let q := if q.isEmpty then (s.vi.lastSearch.map (·.2)).getD [] else q
    let s := { s with overlay := .none, vi := { s.vi with lastSearch := some (backward, q) } }
    if q.isEmpty then bell s
    else match searchHistory backward q s with
      | some s' => ok s'
      | none => bell s
  else if key == .plain .escape || key == Key.ctrl 'c' || key == Key.ctrl 'g' then cancel
  else if key == .plain .backspace || key == Key.ctrl 'h' then
    if q.isEmpty then cancel else ok { s with overlay := .viSearch backward q.dropLast saved }
  else match key.printable? with
    | some c => ok { s with overlay := .viSearch backward (q ++ [c]) saved }
    | none => bell s

end Leanline.Vi
