import Leanline.LineBuffer
import Leanline.History
import Leanline.KillRing
import Leanline.Completion
import Leanline.KeyDecoder
import Leanline.Prefs

/-!
# Editor types

The editor is a pure state machine: `Editor.handleEvent` maps a state and an
input event to a new state, a list of effects for the terminal driver to
perform, and a status saying whether editing continues. All editing logic is
therefore deterministic, testable without a terminal, and amenable to proof.
-/

namespace Leanline

/-- Editing commands. Keymaps bind key sequences to these. -/
inductive Command where
  /-- Insert the character of the key that invoked the command. -/
  | selfInsert
  | insertText (s : String)
  /-- Insert the next key literally, even a control character. -/
  | quotedInsert
  /-- Insert a line break (for multi-line input). -/
  | newline
  | forwardChar | backwardChar | forwardWord | backwardWord
  | beginningOfLine | endOfLine
  | deleteChar | backwardDeleteChar
  /-- Delete under the cursor, or signal end of input on an empty line. -/
  | deleteCharOrEof
  | killLine | backwardKillLine | killWholeLine
  | killWord | backwardKillWord
  /-- Kill the whitespace-delimited word before the cursor. -/
  | unixWordRubout
  | yank | yankPop
  /-- Insert the last word of the previous history entry; repeat to go further back. -/
  | yankLastArg
  | transposeChars | upcaseWord | downcaseWord | capitalizeWord
  | previousHistory | nextHistory | beginningOfHistory | endOfHistory
  /-- Search history for entries starting with the text before the cursor. -/
  | historySearchBackward | historySearchForward
  /-- Incremental search (`C-r` / `C-s`). -/
  | reverseSearchHistory | forwardSearchHistory
  /-- Complete (as configured: list or menu completion). -/
  | complete
  | menuComplete | menuCompleteBackward
  /-- List the candidates without changing the line. -/
  | possibleCompletions
  | undo | redo
  /-- Undo every change made to the line. -/
  | revertLine
  | acceptLine
  | interrupt
  | clearScreen
  | suspend
  /-- Edit the line in `$VISUAL` / `$EDITOR`. -/
  | editInEditor
  | digitArgument (d : Nat)
  /-- Cancel a pending argument or key sequence. -/
  | abort
  /-- Leave vi insert mode. -/
  | viCommandMode
  | bell
  | noop
  deriving DecidableEq, Repr, Inhabited

/-- Key sequences bound to commands. Earlier entries take precedence. -/
abbrev Keymap := List (List Key × Command)

inductive KeymapLookup where
  | command (c : Command)
  | prefixOf
  | unbound
  deriving DecidableEq, Repr

def Keymap.lookup (km : Keymap) (keys : List Key) : KeymapLookup :=
  match km.find? (fun (seq, _) => seq == keys) with
  | some (_, c) => .command c
  | none =>
    if km.any (fun (seq, _) => keys.isPrefixOf seq && keys.length < seq.length) then .prefixOf
    else .unbound

inductive ViMode where
  | insert
  | command
  | replace
  deriving DecidableEq, Repr, Inhabited

/-- The current keymap family. -/
inductive Mode where
  | emacs
  | vi (m : ViMode)
  deriving DecidableEq, Repr, Inhabited

structure SearchState where
  backward : Bool
  query : List Char
  failed : Bool := false
  savedBuf : LineBuffer
  savedNav : HistoryNav
  deriving DecidableEq, Repr, Inhabited

structure MenuState where
  kept : List Grapheme
  after : List Grapheme
  candidates : List Completion
  /-- Index into `candidates`; `candidates.length` stands for the original text. -/
  index : Nat
  original : LineBuffer
  deriving DecidableEq, Repr, Inhabited

/-- Transient sub-modes layered over the main mode. -/
inductive Overlay where
  | none
  | isearch (s : SearchState)
  | menu (m : MenuState)
  | quoted
  /-- Typing a vi `/` or `?` search pattern. -/
  | viSearch (backward : Bool) (query : List Char) (savedBuf : LineBuffer)
  deriving DecidableEq, Repr, Inhabited

/-- What the previous command was, for commands whose behaviour depends on it. -/
inductive LastAction where
  | other
  | insert
  | kill (backward : Bool)
  | yank (len : Nat)
  | yankLastArg (entry : Nat) (len : Nat)
  | complete
  | prefixSearch (pfx : List Grapheme)
  deriving DecidableEq, Repr, Inhabited

inductive ViMotion where
  | left | right
  | wordFwd (big : Bool) | wordBack (big : Bool) | wordEnd (big : Bool)
  | lineStart | firstNonBlank | lineEnd
  | column
  | find (c : Grapheme) (forward : Bool) (till : Bool)
  | repeatFind (reverse : Bool)
  | matchPair
  | wholeLine
  deriving DecidableEq, Repr, Inhabited

inductive ViOperator where
  | delete | change | yank
  deriving DecidableEq, Repr, Inhabited

inductive ViInsertPos where
  | here | after | lineStart | lineEnd
  deriving DecidableEq, Repr, Inhabited

/-- A complete vi command-mode command. Counts default to 1. -/
inductive ViCommand where
  | move (count : Nat) (m : ViMotion)
  | operate (op : ViOperator) (count : Nat) (m : ViMotion)
  | insert (pos : ViInsertPos)
  | substitute (count : Nat)
  | deleteChar (count : Nat)
  | deleteCharBack (count : Nat)
  | replaceChar (count : Nat) (g : Grapheme)
  | replaceMode
  | toggleCase (count : Nat)
  | put (count : Nat) (before : Bool)
  | undo | redo | revert
  | repeatChange (count : Option Nat)
  | historyPrev (count : Nat) | historyNext (count : Nat) | historyOldest
  | search (backward : Bool)
  | searchAgain (reverse : Bool)
  | accept | eof | interrupt | clearScreen | suspend | editInEditor | complete
  | cancel
  deriving DecidableEq, Repr, Inhabited

structure ViChange where
  cmd : ViCommand
  inserted : List Grapheme := []
  deriving DecidableEq, Repr, Inhabited

structure ViState where
  /-- The change `.` repeats. -/
  lastChange : Option ViChange := none
  /-- A change that entered insert mode, with the text typed since. -/
  recording : Option ViChange := none
  lastFind : Option (Grapheme × Bool × Bool) := none
  lastSearch : Option (Bool × List Char) := none
  deriving DecidableEq, Repr, Inhabited

structure EditorState where
  buf : LineBuffer := {}
  nav : HistoryNav := {}
  /-- The full history, newest first (for suggestions and `yank-last-arg`). -/
  history : List String := []
  kill : KillRing := {}
  undoStack : List LineBuffer := []
  redoStack : List LineBuffer := []
  /-- The line as it was when editing started (for `revert-line`). -/
  original : LineBuffer := {}
  mode : Mode := .emacs
  overlay : Overlay := .none
  /-- Keys of an unfinished multi-key binding or vi command. -/
  pending : List Key := []
  /-- Numeric argument (Emacs `M-<digit>`). -/
  arg : Option Nat := none
  last : LastAction := .other
  /-- The current undo group is open: further changes join it. -/
  undoGroup : Bool := false
  lastSearchQuery : List Char := []
  vi : ViState := {}
  deriving DecidableEq, Repr, Inhabited

/-- How the driver should run the completion function. -/
inductive CompletionKind where
  /-- Insert the common prefix, list when ambiguous. -/
  | insert
  | menu (backward : Bool)
  /-- Only list the candidates. -/
  | listOnly
  deriving DecidableEq, Repr, Inhabited

inductive Effect where
  | bell
  | clearScreen
  | listCompletions (items : List String)
  | suspend
  | editInEditor
  deriving DecidableEq, Repr, Inhabited

inductive Status where
  | editing
  | accept (line : String)
  | eof
  | interrupt
  /-- The driver must run the completion function and call `Editor.applyCompletion`. -/
  | complete (kind : CompletionKind)
  deriving DecidableEq, Repr, Inhabited

structure StepResult where
  state : EditorState
  effects : List Effect := []
  status : Status := .editing
  deriving DecidableEq, Repr, Inhabited

/-- Pure configuration of the editor (derived from `Prefs` and `Settings`). -/
structure EditorConfig where
  editMode : EditMode := .emacs
  completionType : CompletionType := .list
  listCompletionsImmediately : Bool := true
  /-- User bindings, consulted before the built-in keymaps. -/
  bindings : Keymap := []
  /-- Keys that expand to other keys (Haskeline's `bind:`). -/
  macros : List (Key × List Key) := []
  suggestions : Bool := false
  prefixHistorySearch : Bool := false
  /-- Password entry: no history, completion, or suggestions. -/
  password : Bool := false
  /-- Whether completion is available at all. -/
  hasCompletion : Bool := true
  /-- Multi-line input: when this returns `false` for the current text,
  Enter inserts a line break instead of accepting. -/
  isComplete : String → Bool := fun _ => true

end Leanline
