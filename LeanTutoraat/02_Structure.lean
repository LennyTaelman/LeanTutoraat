/- Copyright (c) Lenny Taelman, 2025.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

namespace worksheet_02

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


example (x y a b : ℝ) (h1 : x ≤ y) (h2 : a ≤ b) : a * y + b * x ≤ a * x + b * y := by
  -- we first show that y - x ≥ 0
  have h1' : y - x ≥ 0 := by
    calc
      0 ≤ x - x := by algebra
      _ ≤ y - x := by rel [h1]
  -- similarly, b - a ≥ 0
  have h2' : b - a ≥ 0 := by
    calc
      0 ≤ a - a := by algebra
      _ ≤ b - a := by rel [h2]
  -- now `extra` will be able to deduce that (b - a) * (y - x) ≥ 0
  calc
    a * y + b * x ≤ (a * y + b * x) + (b - a) * (y - x) := by extra
    _ = a * x + b * y := by algebra

/-
  This looks inefficient! We are doing the same proof twice. We should extract the
  repeated part into a lemma. Replace the `sorry` below with a correct proof.
-/

lemma sub_nonneg (x y : ℝ) (h : y ≥ x) : 0 ≤ y - x := by
  sorry

example (x y a b : ℝ) (h1 : x ≤ y) (h2 : b ≥ a) : a * y + b * x ≤ a * x + b * y := by
  have h1' : y - x ≥ 0 := by sorry
  have h2' : b - a ≥ 0 := by sorry
  calc
    a * y + b * x ≤ (a * y + b * x) + (b - a) * (y - x) := by extra
    _ = a * x + b * y := by algebra

-- and we can re-use the lemma in other proofs:

-- TODO: example!






example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith [h1]
  have h4 : r ≤ 3 - s := by addarith [h2]
  calc
    r = (r + r) / 2 := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by addarith [h3, h4]
    _ = 3 := by ring

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
