import Leanline

/-!
# Test support

Helpers to run the pure editor on a sequence of keys, as the terminal driver
would, including answering completion requests.
-/

namespace Leanline.Tests

def typeKeys (s : String) : List Key := s.toList.map Key.char

def esc : Key := .plain .escape
def enter : Key := .plain .enter
def tab : Key := .plain .tab
def bs : Key := .plain .backspace
def up : Key := .plain .up
def down : Key := .plain .down
def left : Key := .plain .left
def right : Key := .plain .right

def emacs : EditorConfig := {}
def vi : EditorConfig := { editMode := .vi }

/-- Feed key events one at a time, as the terminal driver does, stopping when
editing ends or completion is requested. Effects are accumulated. -/
def feed (cfg : EditorConfig) (r : StepResult) : List Key → StepResult
  | [] => r
  | k :: ks =>
    let r' := Editor.handleEvent cfg r.state (.key k)
    if r'.status != .editing then { r' with effects := r.effects ++ r'.effects }
    else feed cfg { r' with effects := r.effects ++ r'.effects } ks

/-- Feed keys to a fresh editor. -/
def run (cfg : EditorConfig) (history : List String) (keys : List Key) : StepResult :=
  feed cfg { state := Editor.initial cfg history } keys

/-- Continue from a previous result (dropping its effects). -/
def cont (cfg : EditorConfig) (r : StepResult) (keys : List Key) : StepResult :=
  feed cfg { state := r.state } keys

def text (r : StepResult) : String := r.state.buf.toString
def cursor (r : StepResult) : Nat := r.state.buf.pos

/-- Answer a pending completion request with fixed candidates for the word
before the cursor (as a completion function would). -/
def answer (cfg : EditorConfig) (r : StepResult) (words : List String) : StepResult :=
  match r.status with
  | .complete kind =>
    let (kept, word) := splitWord none [' '] r.state.buf.textBefore
    let cands := (words.filter (Text.isPrefix word ·)).map simpleCompletion
    Editor.applyCompletion cfg kind { kept, candidates := cands } r.state
  | _ => r

end Leanline.Tests
