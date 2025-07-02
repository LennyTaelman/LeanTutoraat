/- Copyright (c) Lenny Taelman, 2025.  All rights reserved. -/
import Mathlib
import Library.Basic

-- NOTE: this also establishes a basic simp tactic
math2001_init

open Real
noncomputable section


example (x : ℝ) (h : x > 0) : x⁻¹ > 0 := by exact inv_pos.mpr h
example (x : ℝ) (h : x > 0) : x⁻¹ > 0 := by positivity
example (x : ℝ) (h : x > 0) : x⁻¹ > 0 := by apply inv_pos.mpr; exact h
example (x : ℝ) (h : x > 0) : x⁻¹ > 0 := by field_simp; exact one_div_pos.mpr h;
example (x : ℝ) (h : x > 0) : x⁻¹ > 0 := by simp_all only [gt_iff_lt, inv_pos];

example (x : ℝ) (h : x > 0) (h2 : y ≥ 0) : x * y ≥ 0 := by simp_all only [gt_iff_lt,
  ge_iff_le, zero_le_mul_left]

example (n : ℕ) : 2 / ((n:ℝ) + 1) > 0 := by positivity

example (n : ℕ) : 3 / ((5 : ℝ) ^ n) > 0 := by positivity
