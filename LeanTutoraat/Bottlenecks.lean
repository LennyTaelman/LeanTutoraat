/- Copyright (c) Lenny Taelman, 2025.  All rights reserved. -/
import Mathlib
import Library.Basic


open Real
noncomputable section

/-
  Things to be considered in lecture 4
-/



/-
  ## Why did we avoid subtraction and division in the proofs above?
-/

-- Verify that `algebra` cannot prove the statement below. Why would that be?
example (n : ℕ) : (n - 1) + 1 = n := by
  sorry

/-
  In fact, in Lean the subtraction of two natural numbers is again a natural
  number. If the result would be negative, it is defined to be `0`.

  So the above statement is *false* for `n = 0`, since the left hand side is `1`.

  However, for integers (or rationals, or reals, ...) subtraction is defined as
  usual. Indeed, verify that `algebra` *can* prove the statement below.
-/

example (n : ℤ) : (n - 1) + 1 = n := by
  sorry


/-
  Exercise:
-/


example (n : ℕ) (h : n ≥ 1) : (n - 1) + 1 = n := by
  induction_from_starting_point n, h with k hk IH
  · rfl
  · algebra





/- # For later use! -/

example (N : ℕ) (h : N ≥ 1) : ∃ n : ℕ, N = n + 1 := by
  induction_from_starting_point N, h with k hk IH
  · use 0; numbers
  · obtain ⟨n, hn⟩ := IH
    use n + 1
    rewrite [hn]
    algebra


/-
  Collection of `minimal' statements that we should be able to handle idiomatically.
-/


example (n : ℕ) (h : n > 0) : n ≥ 1 := by apply h

example (c : ℝ) (h : c > 1) : 1 / c < 1 := by
  have h2 : 1 / c > 0 := by positivity
  calc
    1 / c =  1 * (1 / c) := by algebra
    _ < c * (1 / c) := by rel [h]
    _ = 1 := by algebra

example (c : ℝ) (h : c ≠ 0) : c * (1 / c) = 1 := by algebra


-- this should be `rel [h]` or sth similar?
-- think about inequalities and casts!
example (n : ℕ) (h : n ≥ 5) : (n : ℝ) ≥ 5 := by
  norm_cast


/-
  The examples below feel satisfactory
-/
example (a : ℝ) : a ≥ a := by rfl

example (a : ℝ) : a ≤ a := by rfl

example (a : ℝ) : a = a := by rfl

example (f : ℕ → ℝ) (n m : ℕ): f (n + m) = f (m + n) := by algebra

example (a : ℝ) (k : ℕ) : a ^ k * a ^ k = a ^ (2 * k) := by algebra

example (a : ℝ) (k : ℕ) : a ^ k * a = a ^ (1 + k) := by algebra

example (a b : ℝ) (h : b > 0) : a + b > a := by extra

example (a b : ℝ) (h : b > 0) : a - b < a := by extra

example (n m : ℕ) (a : ℝ) : (n * m : ℕ) * a = (n : ℕ) * (m * a) := by
  algebra

example (n : ℕ) (hn : n ≥ 1) : n + 1 ≥ 2 := by
  calc
    n + 1 ≥ 1 + 1 := by rel [hn]
    _ = 2 := by numbers
