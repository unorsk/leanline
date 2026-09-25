import Leanline.Text
import Leanline.Unicode
import Leanline.Grapheme
import Leanline.LineBuffer
import Leanline.History
import Leanline.KillRing
import Leanline.Completion
import Leanline.Terminal
import Leanline.Key
import Leanline.KeyDecoder
import Leanline.Prefs
import Leanline.Editor
import Leanline.Render
import Leanline.Reader
import Leanline.InputT

/-!
# Leanline

Line editing for Lean programs, in the spirit of Haskell's Haskeline: Emacs
and vi key bindings, persistent history with search, completion, Unicode,
multi-line input, and a plain-line fallback when input is not a terminal.

Run an `InputT` computation with `runInputT` and read lines with
`getInputLine`; see `Examples/Demo.lean` for a complete program.

The editor itself (`Leanline.Editor`) is a pure state machine over key
events; the theorems in `LeanlineTests` are checked on every build.
-/
