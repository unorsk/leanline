import Leanline

/-!
# Theorems: completion

The common prefix inserted on Tab really is a prefix of every candidate, and
escaping of candidates is undone by the word splitter.
-/

namespace Leanline.Tests

/-! ## Longest common prefix -/

theorem commonPrefix_prefix_left (a b : List Char) : commonPrefix a b <+: a := by
  induction a generalizing b with
  | nil => simp [commonPrefix]
  | cons x xs ih =>
    cases b with
    | nil => simp [commonPrefix]
    | cons y ys =>
      simp only [commonPrefix]
      split
      · exact List.cons_prefix_cons.mpr ⟨rfl, ih ys⟩
      · exact List.nil_prefix

theorem commonPrefix_prefix_right (a b : List Char) : commonPrefix a b <+: b := by
  induction a generalizing b with
  | nil => simp [commonPrefix]
  | cons x xs ih =>
    cases b with
    | nil => simp [commonPrefix]
    | cons y ys =>
      simp only [commonPrefix]
      split
      · rename_i h
        have : x = y := by simpa using h
        subst this
        exact List.cons_prefix_cons.mpr ⟨rfl, ih ys⟩
      · exact List.nil_prefix

theorem foldl_commonPrefix (xs : List (List Char)) (init : List Char) :
    xs.foldl commonPrefix init <+: init ∧ ∀ y ∈ xs, xs.foldl commonPrefix init <+: y := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨h1, h2⟩ := ih (commonPrefix init y)
    refine ⟨h1.trans (commonPrefix_prefix_left _ _), ?_⟩
    intro z hz
    cases hz with
    | head => exact h1.trans (commonPrefix_prefix_right _ _)
    | tail _ hz => exact h2 z hz

/-- The text inserted for ambiguous completions is a prefix of every candidate. -/
theorem longestCommonPrefix_prefix (xs : List (List Char)) (x : List Char) (hx : x ∈ xs) :
    longestCommonPrefix xs <+: x := by
  cases xs with
  | nil => cases hx
  | cons y ys =>
    simp only [longestCommonPrefix]
    cases hx with
    | head => exact (foldl_commonPrefix ys x).1
    | tail _ h => exact (foldl_commonPrefix ys y).2 x h

theorem longestCommonPrefix_singleton (x : List Char) : longestCommonPrefix [x] = x := rfl

theorem commonPrefix_self (a : List Char) : commonPrefix a a = a := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [commonPrefix, ih]

/-- Identical candidates complete fully. -/
theorem longestCommonPrefix_replicate (x : List Char) (n : Nat) :
    longestCommonPrefix (x :: List.replicate n x) = x := by
  simp only [longestCommonPrefix]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, commonPrefix_self, ih]

/-! ## Escaping -/

/-- Escaping a candidate and splitting it back off the line is lossless. -/
theorem unescape_escape (e : Char) (needs : Char → Bool) (cs : List Char) :
    unescapeWith (some e) (escapeWith (some e) needs cs) = cs := by
  simp only [unescapeWith]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : (c == e || needs c) = true
    · simp only [escapeWith, h, ↓reduceIte]
      simp [unescapeWith.go, ih]
    · have hce : e ≠ c := by intro hc; subst hc; simp at h
      simp only [escapeWith, h]
      simp [unescapeWith.go, hce, ih]

/-- Without an escape character nothing is escaped. -/
theorem escapeWith_none (needs : Char → Bool) (cs : List Char) : escapeWith none needs cs = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [escapeWith, ih]

/-! ## Examples -/

example : unescapeWith (some '\\') "a\\ b\\".toList = "a b\\".toList := by decide +kernel
example : escapeWith (some '\\') (· == ' ') "a b".toList = "a\\ b".toList := by decide +kernel

example : splitWord (some '\\') [' '] "cat my\\ fi" = ("cat ", "my fi") := by decide +kernel
example : splitWord none [' ', '='] "set x=fo" = ("set x=", "fo") := by decide +kernel
example : longestCommonPrefix ["foobar".toList, "foobaz".toList, "foo".toList] = "foo".toList := by decide +kernel
example : longestCommonPrefix ["abc".toList, "xyz".toList] = [] := by decide +kernel
example : openQuote (some '\\') ['"'] "echo \"my fi".toList 0 none = some (5, '"') := by decide +kernel
example : openQuote (some '\\') ['"'] "echo \"a\" b".toList 0 none = none := by decide +kernel

/-- Run a completion function in `Id`. -/
def completeIn (f : CompletionFunc Id) (before : String) (after : String := "") : CompletionResult :=
  Id.run (f { before, after })

example : completeIn (completeFromList ["help", "hello", "quit"]) "he" =
    { kept := "", candidates := [simpleCompletion "help", simpleCompletion "hello"] } := by decide +kernel

example : completeIn (completeFromList ["help", "quit"]) "run q" =
    { kept := "run ", candidates := [simpleCompletion "quit"] } := by decide +kernel

/-- Candidates are escaped for the line (a space in a file name gets a
backslash) while their display form stays readable. -/
example : completeIn (completeWord (some '\\') [' '] fun _ => pure [simpleCompletion "my file"]) "cat my" =
    { kept := "cat ", candidates := [{ replacement := "my\\ file", display := "my file" }] } := by decide +kernel

/-- The word handed to the completer is unescaped (and escaped again on the way back). -/
example : completeIn (completeWord (some '\\') [' '] fun w => pure [simpleCompletion w]) "cat my\\ f" =
    { kept := "cat ", candidates := [{ replacement := "my\\ f", display := "my f" }] } := by decide +kernel

/-- Inside quotes nothing is escaped except the quote, and finished words are closed. -/
example : completeIn (completeQuotedWord (some '\\') ['"'] (fun _ => pure [simpleCompletion "my file"]) noCompletion)
    "cat \"my" =
    { kept := "cat \"", candidates := [{ replacement := "my file\"", display := "my file" }] } := by decide +kernel

example : completeIn (fallbackCompletion noCompletion (completeFromList ["x"])) "" =
    { kept := "", candidates := [simpleCompletion "x"] } := by decide +kernel

end Leanline.Tests
