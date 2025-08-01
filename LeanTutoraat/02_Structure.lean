/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Proofs with structure -/


/-! ## Establishing intermediate results with `have` -/





-- intro


-- useful, since you can call them in `rw` and `rel`
-- also useful as they are also silently available (e.g. when the positivity of
-- something is needed)



/-
  The inequality below is called the "rearrangement inequality". It abstracts
  the following intuitively obvious fact: if `b > a`, and you need to
  choose between either
  - picking `b` valuable and `a` worthless items, or
  - picking `a` valuable and `b` worthless items,
  then the first option is clearly better.
-/
example (x y a b : ℝ) (h1 : y ≥ x) (h2 : b ≥ a) : a * y + b * x ≤ a * x + b * y := by
  have h1' : y - x ≥ 0 := by addarith [h1]
  have h2' : b - a ≥ 0 := by addarith [h2]
  calc
    a * y + b * x ≤ (a * y + b * x) + (b - a) * (y - x) := by extra
    _ = a * x + b * y := by ring


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring


example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by sorry -- justify with one tactic
  have h4 : r ≤ 3 - s := by sorry -- justify with one tactic
  calc
    r = (r + r) / 2 := by sorry -- justify with one tactic
    _ ≤ (3 - s + (3 + s)) / 2 := by sorry -- justify with one tactic
    _ = 3 := by sorry -- justify with one tactic

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring
  cancel 2 at h3


example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  sorry

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  sorry

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  sorry

/-! # Exercises -/


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  sorry

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  sorry

example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  sorry


/-! ## Invoking a lemma with `apply` -/


/-! ## Proving ∀-statements with `intro` -/


/-! ## Proving ∃-statements with `use` -/
