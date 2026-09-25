import LeanlineTests.Support

/-!
# Theorems: vi mode

Command-mode behaviour checked by evaluation in the kernel, plus general
properties of the command parser.
-/

namespace Leanline.Tests

open Editor

/-- Type `line` in insert mode, press Escape, then run `cmds` in command mode. -/
def viRun (line : String) (cmds : List Key) (history : List String := []) : StepResult :=
  run vi history (typeKeys line ++ [esc] ++ cmds)

def viCmd (line : String) (cmds : String) (history : List String := []) : StepResult :=
  viRun line (typeKeys cmds) history

/-! ## Modes -/

example : (run vi [] []).state.mode = .vi .insert := by decide +kernel
example : (viCmd "abc" "").state.mode = .vi .command := by decide +kernel
/-- Leaving insert mode moves the cursor onto the last character. -/
example : cursor (viCmd "abc" "") = 2 := by decide +kernel
example : text (viCmd "abc" "ix") = "abxc" := by decide +kernel
example : text (viCmd "abc" "ax") = "abcx" := by decide +kernel
example : text (viCmd "abc" "0ax") = "axbc" := by decide +kernel
example : text (viCmd "  abc" "Ix") = "x  abc" := by decide +kernel
example : text (viCmd "abc" "0Ax") = "abcx" := by decide +kernel
/-- An Escape typed quickly before a key arrives as a Meta key; it still works. -/
example : text (run vi [] (typeKeys "abc" ++ [Key.alt '0'] ++ typeKeys "x")) = "bc" := by decide +kernel

/-! ## Motions -/

example : cursor (viCmd "hello world" "0") = 0 := by decide +kernel
example : cursor (viCmd "hello world" "0$") = 10 := by decide +kernel
example : cursor (viCmd "hello world" "0w") = 6 := by decide +kernel
example : cursor (viCmd "hello world" "b") = 6 := by decide +kernel
example : cursor (viCmd "hello world" "0e") = 4 := by decide +kernel
example : cursor (viCmd "foo.bar baz" "0w") = 3 := by decide +kernel
example : cursor (viCmd "foo.bar baz" "0W") = 8 := by decide +kernel
example : cursor (viCmd "foo.bar baz" "0E") = 6 := by decide +kernel
example : cursor (viCmd "hello" "0lll") = 3 := by decide +kernel
example : cursor (viCmd "hello" "0lllllll") = 4 := by decide +kernel
example : cursor (viCmd "hello" "0hh") = 0 := by decide +kernel
example : cursor (viCmd "  indented" "0^") = 2 := by decide +kernel
example : cursor (viCmd "abcdef" "04|") = 3 := by decide +kernel
example : cursor (viCmd "one two three four" "03w") = 14 := by decide +kernel
example : cursor (viCmd "a,b,c,d" "0f,") = 1 := by decide +kernel
example : cursor (viCmd "a,b,c,d" "0f,;;") = 5 := by decide +kernel
example : cursor (viCmd "a,b,c,d" "0f,;;,") = 3 := by decide +kernel
example : cursor (viCmd "a,b,c,d" "0t,") = 0 := by decide +kernel
example : cursor (viCmd "a,b,c,d" "0t,;") = 2 := by decide +kernel
example : cursor (viCmd "a,b,c,d" "F,") = 5 := by decide +kernel
example : cursor (viCmd "a,b,c,d" "T,") = 6 := by decide +kernel
example : cursor (viCmd "a,b,c,d" "02f,") = 3 := by decide +kernel
example : cursor (viCmd "f(a[b]c)d" "0%") = 7 := by decide +kernel
example : cursor (viCmd "f(a[b]c)d" "0%%") = 1 := by decide +kernel
/-- A failed motion rings the bell and leaves the cursor alone. -/
example : (viCmd "abc" "0fz").effects = [.bell] := by decide +kernel

/-! ## Operators -/

example : text (viCmd "hello world" "0dw") = "world" := by decide +kernel
example : text (viCmd "hello world" "0de") = " world" := by decide +kernel
example : text (viCmd "hello world" "db") = "hello d" := by decide +kernel
example : text (viCmd "hello world" "0wd$") = "hello " := by decide +kernel
example : text (viCmd "hello world" "0wD") = "hello " := by decide +kernel
example : text (viCmd "hello world" "d0") = "d" := by decide +kernel
example : text (viCmd "hello world" "dd") = "" := by decide +kernel
example : text (viCmd "a b c d" "02dw") = "c d" := by decide +kernel
example : text (viCmd "a b c d" "0d2w") = "c d" := by decide +kernel
example : text (viCmd "a b c d e f g" "02d3w") = "g" := by decide +kernel
example : text (viCmd "key = value" "0dt=") = "= value" := by decide +kernel
example : text (viCmd "key = value" "0df=") = " value" := by decide +kernel
example : text (viCmd "key = value" "dF=") = "key e" := by decide +kernel
example : text (viCmd "key = value" "dT=") = "key =e" := by decide +kernel
/-- Off a bracket, `%` uses the first bracket after the cursor. -/
example : text (viCmd "f(a[b]c)d" "0fad%") = "f(c)d" := by decide +kernel
example : text (viCmd "f(a[b]c)d" "0f(d%") = "fd" := by decide +kernel
/-- `cw` changes to the end of the word (like `ce`), not to the next word. -/
example : text (run vi [] (typeKeys "hello world" ++ [esc] ++ typeKeys "0cwbye" ++ [esc])) = "bye world" := by
  decide +kernel
example : text (run vi [] (typeKeys "hello world" ++ [esc] ++ typeKeys "0wCthere" ++ [esc])) = "hello there" := by
  decide +kernel
example : text (run vi [] (typeKeys "hello world" ++ [esc] ++ typeKeys "ccnew" ++ [esc])) = "new" := by decide +kernel
example : text (run vi [] (typeKeys "hello world" ++ [esc] ++ typeKeys "Snew" ++ [esc])) = "new" := by decide +kernel
example : text (run vi [] (typeKeys "hello" ++ [esc] ++ typeKeys "0sj" ++ [esc])) = "jello" := by decide +kernel
example : text (run vi [] (typeKeys "hello" ++ [esc] ++ typeKeys "03sj" ++ [esc])) = "jlo" := by decide +kernel
/-- Yank does not change the line; put inserts after (`p`) or before (`P`). -/
example : text (viCmd "abc" "0ywP") = "abcabc" := by decide +kernel
example : text (viCmd "one two" "0ywwP") = "one one two" := by decide +kernel
example : text (viCmd "abc" "yyp") = "abcabc" := by decide +kernel
example : text (viCmd "abc" "0Yp") = "aabcbc" := by decide +kernel
example : text (viCmd "abc" "0xp") = "bac" := by decide +kernel
example : text (viCmd "abc" "0x3p") = "baaac" := by decide +kernel
example : cursor (viCmd "abc" "0xp") = 1 := by decide +kernel

/-! ## Simple commands -/

example : text (viCmd "hello" "0x") = "ello" := by decide +kernel
example : text (viCmd "hello" "03x") = "lo" := by decide +kernel
example : text (viCmd "hello" "X") = "helo" := by decide +kernel
example : text (viCmd "hello" "2X") = "heo" := by decide +kernel
example : text (viCmd "hello" "0rj") = "jello" := by decide +kernel
example : text (viCmd "hello" "03rx") = "xxxlo" := by decide +kernel
example : (viCmd "hi" "05rx").effects = [.bell] := by decide +kernel
example : text (viCmd "hello" "0~~") = "HEllo" := by decide +kernel
example : text (viCmd "hello" "05~") = "HELLO" := by decide +kernel
example : text (run vi [] (typeKeys "hello" ++ [esc] ++ typeKeys "0Rjel" ++ [esc])) = "jello" := by decide +kernel
example : text (run vi [] (typeKeys "hi" ++ [esc] ++ typeKeys "0Rhey" ++ [esc])) = "hey" := by decide +kernel

/-! ## Undo, redo and repeat -/

example : text (viCmd "hello" "u") = "" := by decide +kernel
example : text (viCmd "hello world" "0dwu") = "hello world" := by decide +kernel
example : text (viCmd "hello world" "0dwu" |> (cont vi · [Key.ctrl 'r'])) = "world" := by decide +kernel
example : text (viCmd "a b c" "0dwdwuu") = "a b c" := by decide +kernel
/-- An insert session is a single undo step. -/
example : text (run vi [] (typeKeys "abc" ++ [esc] ++ typeKeys "Adef" ++ [esc] ++ typeKeys "u")) = "abc" := by
  decide +kernel
example : text (viCmd "abc" "0xxU") = "" := by decide +kernel
example : text (viCmd "one two three" "0dw.") = "three" := by decide +kernel
example : text (viCmd "a b c d e" "0dw2.") = "d e" := by decide +kernel
example : text (viCmd "abcdef" "0x..") = "def" := by decide +kernel
example : text (viCmd "abcdef" "02x.") = "ef" := by decide +kernel
example : text (viCmd "hello" "0rj.") = "jello" := by decide +kernel
/-- `.` repeats a change together with the text typed after it. -/
example : text (run vi [] (typeKeys "one two three" ++ [esc] ++ typeKeys "0cwX" ++ [esc] ++ typeKeys "w.")) =
    "X X three" := by decide +kernel
example : text (run vi [] (typeKeys "a" ++ [esc] ++ typeKeys "A!" ++ [esc] ++ typeKeys "..")) = "a!!!" := by
  decide +kernel
example : (viCmd "abc" ".").effects = [.bell] := by decide +kernel

/-! ## History -/

def hist : List String := ["newest", "middle", "oldest"]

example : text (viCmd "" "k" hist) = "newest" := by decide +kernel
example : cursor (viCmd "" "k" hist) = 0 := by decide +kernel
example : text (viCmd "" "kk" hist) = "middle" := by decide +kernel
example : text (viCmd "" "2k" hist) = "middle" := by decide +kernel
example : text (viCmd "" "kkj" hist) = "newest" := by decide +kernel
example : text (viCmd "" "G" hist) = "oldest" := by decide +kernel
example : text (viCmd "" "-" hist) = "newest" := by decide +kernel
/-- `/` searches older entries; `n` repeats; `N` reverses. -/
example : text (run vi ["a foo", "bar", "b foo"] ([esc] ++ typeKeys "/foo" ++ [enter])) = "a foo" := by decide +kernel
example : text (run vi ["a foo", "bar", "b foo"] ([esc] ++ typeKeys "/foo" ++ [enter] ++ typeKeys "n")) = "b foo" := by
  decide +kernel
example : text (run vi ["a foo", "bar", "b foo"] ([esc] ++ typeKeys "/foo" ++ [enter] ++ typeKeys "nN")) = "a foo" := by
  decide +kernel
example : (Editor.view vi (run vi [] ([esc] ++ typeKeys "/fo")).state).prompt = some "/" := by decide +kernel
example : text (run vi ["abc"] (typeKeys "draft" ++ [esc] ++ typeKeys "/zz" ++ [esc])) = "draft" := by decide +kernel

/-! ## Finishing -/

example : (viRun "ls" [enter]).status = .accept "ls" := by decide +kernel
example : (run vi [] (typeKeys "ls" ++ [enter])).status = .accept "ls" := by decide +kernel
example : (viRun "" [Key.ctrl 'd']).status = .eof := by decide +kernel
example : (run vi [] [Key.ctrl 'd']).status = .eof := by decide +kernel
example : (viRun "x" [Key.ctrl 'c']).status = .interrupt := by decide +kernel
example : (viRun "x" (typeKeys "v")).effects = [.editInEditor] := by decide +kernel
example : (viRun "x" [tab]).status = .complete .insert := by decide +kernel
/-- Insert-mode editing keys. -/
example : text (run vi [] (typeKeys "hello world" ++ [Key.ctrl 'w'])) = "hello " := by decide +kernel
example : text (run vi [] (typeKeys "hello world" ++ [Key.ctrl 'u'])) = "" := by decide +kernel
example : text (run vi [] (typeKeys "hello" ++ [bs, bs])) = "hel" := by decide +kernel

/-! ## The command parser -/

open Vi in
example : parse (typeKeys "3dw") = .done (.operate .delete 3 (.wordFwd false)) := by decide +kernel
open Vi in
example : parse (typeKeys "2d3w") = .done (.operate .delete 6 (.wordFwd false)) := by decide +kernel
open Vi in
example : parse (typeKeys "d") = .more := by decide +kernel
open Vi in
example : parse (typeKeys "df") = .more := by decide +kernel
open Vi in
example : parse (typeKeys "dfx") = .done (.operate .delete 1 (.find (Grapheme.ofChar 'x') true false)) := by
  decide +kernel
open Vi in
example : parse (typeKeys "12") = .more := by decide +kernel
open Vi in
example : parse (typeKeys "dq") = .invalid := by decide +kernel
open Vi in
example : parse (typeKeys "r") = .more := by decide +kernel
open Vi in
example : parse (typeKeys "rZ") = .done (.replaceChar 1 (Grapheme.ofChar 'Z')) := by decide +kernel
open Vi in
example : parse (typeKeys "cc") = .done (.operate .change 1 .wholeLine) := by decide +kernel
open Vi in
example : parse (typeKeys "0") = .done (.move 1 .lineStart) := by decide +kernel
open Vi in
example : parse (typeKeys "10l") = .done (.move 10 .right) := by decide +kernel

def isDone : Vi.Parse → Bool
  | .done _ => true
  | _ => false

open Vi in
/-- Every simple command key is recognised on its own. -/
theorem parse_single_complete :
    ∀ c ∈ "iaIAsSCDYxXR~pPu.kj-+G/?nNvhlwbeWBE0^$|%;,".toList, isDone (parse [Key.char c]) := by
  decide +kernel

open Vi in
/-- Operators and find motions always wait for more keys. -/
theorem parse_pending :
    ∀ c ∈ "dcyfFtTr".toList, parse [Key.char c] = .more := by
  decide +kernel

open Vi in
/-- A count never changes whether a command is complete. -/
theorem parse_count_irrelevant :
    ∀ c ∈ "xXwbe$~pP".toList, ∀ d ∈ "123456789".toList,
      isDone (parse [Key.char d, Key.char c]) := by
  decide +kernel

end Leanline.Tests
