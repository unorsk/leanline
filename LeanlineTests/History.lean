import Leanline

/-!
# Theorems: history

Size bounds, duplicate policies, navigation, and the file format.
-/

namespace Leanline.Tests

open History

/-! ## Size bounds -/

theorem size_enforceLimit (h : History) (n : Nat) (hmax : h.maxSize = some n) :
    h.enforceLimit.size ≤ n := by
  simp [enforceLimit, hmax, History.size]
  omega

/-- A bounded history never grows beyond its bound. -/
theorem size_add_le (h : History) (line : String) (n : Nat) (hmax : h.maxSize = some n) :
    (h.add line).size ≤ n :=
  size_enforceLimit _ n hmax

theorem size_addWith_le (policy : DuplicatePolicy) (h : History) (line : String) (n : Nat)
    (hmax : h.maxSize = some n) (hsize : h.size ≤ n) : (h.addWith policy line).size ≤ n := by
  cases policy with
  | alwaysAdd => exact size_add_le h line n hmax
  | ignoreConsecutive =>
    simp only [addWith, addUnlessConsecutiveDupe]
    split
    · exact hsize
    · exact size_add_le h line n hmax
  | ignoreAll => exact size_enforceLimit _ n hmax

theorem size_stifle (h : History) (n : Nat) : (h.stifle (some n)).size ≤ n :=
  size_enforceLimit _ n rfl

/-- An unbounded history keeps every line. -/
theorem size_add_unbounded (h : History) (line : String) (hmax : h.maxSize = none) :
    (h.add line).size = h.size + 1 := by
  simp [add, enforceLimit, hmax, History.size]

/-! ## The newest entry -/

def Positive (h : History) : Prop := ∀ n, h.maxSize = some n → 0 < n

theorem head_enforceLimit (h : History) (e : String) (rest : List String) (hpos : Positive h)
    (he : h.entries = e :: rest) : h.enforceLimit.entries.head? = some e := by
  unfold enforceLimit
  split
  · rename_i n hn
    have := hpos n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [he]
  · simp [he]

/-- After `add`, the line is the newest entry. -/
theorem newest_add (h : History) (line : String) (hpos : Positive h) :
    (h.add line).newestFirst.head? = some line :=
  head_enforceLimit { h with entries := line :: h.entries } line h.entries hpos rfl

/-- Whatever the policy, the added line becomes the newest entry. -/
theorem newest_addWith (policy : DuplicatePolicy) (h : History) (line : String) (hpos : Positive h)
    (hhead : h.entries.head? = some line ∨ policy ≠ .ignoreConsecutive) :
    (h.addWith policy line).newestFirst.head? = some line := by
  cases policy with
  | alwaysAdd => exact newest_add h line hpos
  | ignoreConsecutive =>
    simp only [addWith, addUnlessConsecutiveDupe]
    split
    · rename_i hh; simpa [newestFirst] using hh
    · exact newest_add h line hpos
  | ignoreAll =>
    exact head_enforceLimit { h with entries := line :: h.entries.filter (· != line) } line _ hpos rfl

/-! ## Duplicate policies -/

/-- Adding the same line twice in a row records it once. -/
theorem addUnlessConsecutiveDupe_twice (h : History) (line : String) (hpos : Positive h) :
    (h.addUnlessConsecutiveDupe line).addUnlessConsecutiveDupe line = h.addUnlessConsecutiveDupe line := by
  unfold addUnlessConsecutiveDupe
  by_cases hh : h.entries.head? = some line
  · simp [hh]
  · have hnew := newest_add h line hpos
    simp only [newestFirst] at hnew
    simp [hh, hnew]

/-- With `ignoreAll`, a line occurs exactly once after being added. -/
theorem count_addRemovingAllDupes (h : History) (line : String) (hpos : Positive h) :
    (h.addRemovingAllDupes line).entries.count line = 1 := by
  have hnotin : line ∉ h.entries.filter (· != line) := by simp
  have hcount : (h.entries.filter (· != line)).count line = 0 := List.count_eq_zero.mpr hnotin
  unfold addRemovingAllDupes enforceLimit
  split
  · rename_i n hn
    have := hpos n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [List.take_succ_cons, List.count_cons_self]
    have : (List.take k (h.entries.filter (· != line))).count line = 0 :=
      List.count_eq_zero.mpr fun hm => hnotin (List.mem_of_mem_take hm)
    omega
  · simp [List.count_cons_self, hcount]

/-! ## Navigation -/

/-- Stepping back and then forward returns to the line being edited. -/
theorem forward_back (nav nav' : HistoryNav) (current e : String) (h : nav.back current = some (e, nav')) :
    nav'.forward e = some (current, nav) := by
  obtain ⟨older, newer⟩ := nav
  cases older with
  | nil => simp [HistoryNav.back] at h
  | cons x rest =>
    simp only [HistoryNav.back, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- Stepping forward and then back returns to the entry. -/
theorem back_forward (nav nav' : HistoryNav) (current e : String) (h : nav.forward current = some (e, nav')) :
    nav'.back e = some (current, nav) := by
  obtain ⟨older, newer⟩ := nav
  cases newer with
  | nil => simp [HistoryNav.forward] at h
  | cons x rest =>
    simp only [HistoryNav.forward, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- Navigation never loses or invents entries: the timeline (oldest to
newest, with the displayed line in place) is unchanged by a step. -/
def timeline (nav : HistoryNav) (current : String) : List String :=
  nav.older.reverse ++ [current] ++ nav.newer

theorem timeline_back (nav nav' : HistoryNav) (current e : String) (h : nav.back current = some (e, nav')) :
    timeline nav' e = timeline nav current := by
  obtain ⟨older, newer⟩ := nav
  cases older with
  | nil => simp [HistoryNav.back] at h
  | cons x rest =>
    simp only [HistoryNav.back, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [timeline]

theorem toOldest_older (nav : HistoryNav) (current : String) : (nav.toOldest current).2.older = [] := by
  unfold HistoryNav.toOldest
  split <;> simp_all

theorem toNewest_newer (nav : HistoryNav) (current : String) : (nav.toNewest current).2.newer = [] := by
  unfold HistoryNav.toNewest
  split <;> simp_all

/-! ## File format -/

/-- Escaping is undone by unescaping, for every entry. -/
theorem unescape_escape (cs : List Char) : unescapeChars (escapeChars cs) = cs := by
  unfold unescapeChars
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = '\\'
    · subst h1; simp [escapeChars, escapeChar, unescapeAux, unescapeOne, ih]
    by_cases h2 : c = '\n'
    · subst h2; simp [escapeChars, escapeChar, unescapeAux, unescapeOne, ih]
    by_cases h3 : c = '\r'
    · subst h3; simp [escapeChars, escapeChar, unescapeAux, unescapeOne, ih]
    simp [escapeChars, escapeChar, unescapeAux, h1, h2, h3, ih]

theorem unescapeEntry_escapeEntry (s : String) : unescapeEntry (escapeEntry s) = s := by
  simp [unescapeEntry, escapeEntry, unescape_escape]

/-- Escaped entries never contain a line break, so one entry is one line. -/
theorem newline_not_mem_escape (cs : List Char) : '\n' ∉ escapeChars cs := by
  induction cs with
  | nil => simp [escapeChars]
  | cons c cs ih =>
    simp only [escapeChars, escapeChar, List.mem_append, not_or]
    refine ⟨?_, ih⟩
    by_cases h1 : c = '\\'
    · simp [h1]
    by_cases h2 : c = '\n'
    · simp [h2]
    by_cases h3 : c = '\r'
    · simp [h3]
    simp [h1, h2, h3, Ne.symm h2]

/-! ## Examples (checked by evaluation in the kernel) -/

example : (History.parse "one\ntwo\n").newestFirst = ["two", "one"] := by decide
example : (History.parse "a\r\n\nb\n").oldestFirst = ["a", "b"] := by decide
example : (History.parse "x\\ny\n").newestFirst = ["x\ny"] := by decide
example : (History.parse "C:\\temp\n").newestFirst = ["C:\\temp"] := by decide
example : ({ entries := ["b", "a"] } : History).serialize = "a\nb\n" := by decide
example : ({ entries := ["multi\nline", "back\\slash"] } : History).serialize = "back\\\\slash\nmulti\\nline\n" := by decide
example : (History.parse ({ entries := ["multi\nline", "c:\\x", "plain"] } : History).serialize).entries =
    ["multi\nline", "c:\\x", "plain"] := by decide
example : (History.parse "1\n2\n3\n4\n" (some 2)).oldestFirst = ["3", "4"] := by decide
example : ((History.empty.add "a").add "b").newestFirst = ["b", "a"] := by decide
example : ((History.empty.addUnlessConsecutiveDupe "a").addUnlessConsecutiveDupe "a").size = 1 := by decide
example : (((History.empty.add "a").add "b").addRemovingAllDupes "a").newestFirst = ["a", "b"] := by decide
example : ((({ maxSize := some 2 } : History).add "a").add "b" |>.add "c").newestFirst = ["c", "b"] := by decide
example : (({ entries := ["c", "b", "a"] } : History).stifle (some 1)).newestFirst = ["c"] := by decide

end Leanline.Tests
