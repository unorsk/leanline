import Leanline.Editor.Vi

/-!
# Editor

The entry points of the pure editor: `handleEvent` advances the state by one
input event, `applyCompletion` feeds back completion results, and `view`
describes what should be on the screen.
-/

namespace Leanline.Editor

/-- Handle a key while an incremental search is active. -/
def isearchKey (cfg : EditorConfig) (s : EditorState) (ss : SearchState) (key : Key)
    (dispatch : EditorState → Key → StepResult) : StepResult :=
  let leave := { s with overlay := .none }
  if key == Key.ctrl 'r' || key == Key.ctrl 's' then
    let backward := key == Key.ctrl 'r'
    let q := if ss.query.isEmpty then s.lastSearchQuery else ss.query
    searchStep s { ss with backward, query := q } (skipCurrent := !ss.query.isEmpty)
  else if key == .plain .backspace || key == Key.ctrl 'h' then
    let q := ss.query.dropLast
    let base := { s with buf := ss.savedBuf, nav := ss.savedNav }
    searchStep base { ss with query := q } false
  else if key == Key.ctrl 'g' then
    ok { s with overlay := .none, buf := ss.savedBuf, nav := ss.savedNav }
  else if key == .plain .escape then ok leave
  else if key == .plain .enter || key == Key.ctrl 'j' then
    runCommand cfg .acceptLine key leave
  else match key.printable? with
    | some c => searchStep s { ss with query := ss.query ++ [c] } false
    | none => dispatch leave key

/-- Handle a key while cycling through menu completions. -/
def menuKey (cfg : EditorConfig) (s : EditorState) (ms : MenuState) (key : Key)
    (dispatch : EditorState → Key → StepResult) : StepResult :=
  let km := match s.mode with
    | .emacs => Keymaps.emacs
    | .vi _ => Keymaps.viInsert
  let total := ms.candidates.length + 1
  let go (i : Nat) := ok { s with buf := menuShow ms i, overlay := .menu { ms with index := i } }
  match lookupKeys cfg km [key] with
  | .command .complete | .command .menuComplete => go ((ms.index + 1) % total)
  | .command .menuCompleteBackward => go ((ms.index + total - 1) % total)
  | _ => dispatch { s with overlay := .none } key

/-- Handle a key with no overlay active. -/
def dispatch (cfg : EditorConfig) (s : EditorState) (key : Key) : StepResult :=
  match s.mode with
  | .emacs => keymapKey cfg Keymaps.emacs s key
  | .vi .command => Vi.commandKey cfg s key
  | .vi .insert =>
    -- An Escape typed quickly before another key arrives as a Meta key;
    -- treat it as leaving insert mode followed by that key.
    if key.mods.alt && s.pending.isEmpty && lookupKeys cfg Keymaps.viInsert [key] == .unbound then
      let s' := (runCommand cfg .viCommandMode (.plain .escape) s).state
      Vi.commandKey cfg s' { key with mods := { key.mods with alt := false } }
    else keymapKey cfg Keymaps.viInsert s key
  | .vi .replace =>
    if key == .plain .backspace || key == Key.ctrl 'h' then ok { s with buf := s.buf.moveLeft }
    else keymapKey cfg Keymaps.viInsert s key

/-- Handle one key. -/
def handleKey (cfg : EditorConfig) (s : EditorState) (key : Key) : StepResult :=
  match s.overlay with
  | .none => dispatch cfg s key
  | .quoted =>
    let s := { s with overlay := .none }
    match literalChar key with
    | some c => recordUndo .selfInsert s { state := { s with buf := s.buf.insertChar c, arg := none } }
    | none => bell s
  | .isearch ss => isearchKey cfg s ss key (dispatch cfg)
  | .menu ms => menuKey cfg s ms key (dispatch cfg)
  | .viSearch backward q saved => Vi.searchKey s backward q saved key

/-- Run keys in order, stopping when editing ends or completion is requested. -/
def handleKeys (cfg : EditorConfig) (s : EditorState) : List Key → StepResult
  | [] => ok s
  | k :: ks =>
    let r := handleKey cfg s k
    if r.status != .editing then r
    else
      let r' := handleKeys cfg r.state ks
      { r' with effects := r.effects ++ r'.effects }

/-- Advance the editor by one input event. -/
def handleEvent (cfg : EditorConfig) (s : EditorState) (e : InputEvent) : StepResult :=
  match e with
  | .paste text =>
    match s.overlay with
    | .viSearch backward q saved => ok { s with overlay := .viSearch backward (q ++ text.toList) saved }
    | .isearch ss => searchStep s { ss with query := ss.query ++ text.toList } false
    | _ =>
      let s := { s with overlay := .none }
      let s := if s.mode == .vi .command then { s with mode := .vi .insert } else s
      runCommand cfg (.insertText text) (.plain .escape) s
  | .key k =>
    match cfg.macros.lookup k with
    | some ks => handleKeys cfg s ks
    | none => handleKey cfg s k

/-- What the screen should show. -/
structure View where
  /-- Replaces the program's prompt (search modes). -/
  prompt : Option String := none
  /-- The text and cursor to display. -/
  buf : LineBuffer
  /-- Dimmed text shown after the line (history suggestion). -/
  hint : List Grapheme := []
  deriving Repr

def view (cfg : EditorConfig) (s : EditorState) : View :=
  match s.overlay with
  | .isearch ss => { prompt := some (searchPrompt ss), buf := s.buf }
  | .viSearch backward q _ =>
    { prompt := some (if backward then "/" else "?"), buf := LineBuffer.ofLists (graphemes q) [] }
  | _ => { buf := s.buf, hint := (suggestion cfg s).getD [] }

/-- Replace the whole line (after editing it in an external editor). -/
def replaceLine (text : String) (s : EditorState) : EditorState :=
  let b := LineBuffer.ofString text
  if b == s.buf then s
  else { s with buf := b, undoStack := s.buf :: s.undoStack, redoStack := [], undoGroup := false }

end Leanline.Editor
