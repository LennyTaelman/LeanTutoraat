/- Copyright (c) Lenny Taelman, 2025.  All rights reserved. -/
import Mathlib
import Library.Basic

-- NOTE: this also establishes a basic simp tactic
math2001_init

open Real
noncomputable section



/-
  Collection of `minimal' statements that we should be able to handle idiomatically.
-/


example (n : ℕ) (h : n > 0) : n ≥ 1 := by apply h

example (c : ℝ) (h : c > 1) : 1 / c < 1 := by
  have h2 : 1 / c > 0 := by positivity
  calc
    1 / c =  1 * (1 / c) := by ring
    _ < c * (1 / c) := by rel [h]
    _ = 1 := by field_simp

example (c : ℝ) (h : c ≠ 0) : c * (1 / c) = 1 := by field_simp


/-
  The examples below feel satisfactory
-/
example (a : ℝ) : a ≥ a := by rfl

example (a : ℝ) : a ≤ a := by rfl

example (a : ℝ) : a = a := by rfl

example (f : ℕ → ℝ) (n m : ℕ): f (n + m) = f (m + n) := by ring

example (a : ℝ) (k : ℕ) : a ^ k * a ^ k = a ^ (2 * k) := by ring

example (a : ℝ) (k : ℕ) : a ^ k * a = a ^ (1 + k) := by ring

example (a b : ℝ) (h : b > 0) : a + b > a := by extra

example (a b : ℝ) (h : b > 0) : a - b < a := by extra

example (n m : ℕ) (a : ℝ) : (n * m : ℕ) * a = (n : ℕ) * (m * a) := by
  push_cast
  ring
