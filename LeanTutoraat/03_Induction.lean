/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

namespace Nat






example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case: 2 ^ 0 ≥ 0 + 1
    numbers
  · -- inductive step: 2 ^ (k + 1) ≥ (k + 1) + 1
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra



/-
  Sometimes we want to prove something for all n ≥ C,
  and hence want to start induction at n = C.

  The tactic `induction_from_starting_point n, hn with k hk IH`
  - takes the variable `n` on which we want to do induction
  - takes the hypothesis `hn` stating that `n ≥ C`
  - creates a base case for `n = C`
  - creates an inductive step for `n = k + 1` assuming the induction
    hypothesis IH that the statement holds for `n = k`
-/

example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : ∃ C : ℕ, ∀ n : ℕ, n ≥ C → 2 ^ n ≥ n ^ 2 := by
  use sorry -- replace sorry with a correct choice of C
  intro n hn
  -- we now need to prove that for all n ≥ C we have 2 ^ n ≥ n ^ 2
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    sorry
  · -- inductive step
    sorry


-- TODO: add examples with ∑ over {0..n}

/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  sorry

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  sorry

example : ∃ C : ℕ, ∀ n : ℕ, n ≥ C → (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  sorry


/-! # Finite sums -/


/-
  The code below defines s1 : ℕ → ℝ recursively. We have
  s1 n = 1 + 2 + ... + n
-/

def s1 (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => (s1 n) + (n + 1)

/-
  To be able to prove things about s1, we can use the following two lemmas:
-/

lemma s1_zero : s1 0 = 0 := by rfl

lemma s1_succ (n : ℕ) : s1 (n + 1) = s1 n + (n + 1) := by rfl

/-
  We can now prove that s1 n = n * (n + 1) / 2. We will do this by induction.
-/

lemma s1_formula (n : ℕ) : s1 n = n * (n + 1) / 2 := by
  simple_induction n with k IH
  · -- base case: s1 0 = ...
    rw [s1_zero]
    numbers
  · -- inductive step: s1 (k + 1) = ...
    rw [s1_succ]
    rw [IH]
    ring


/-
  We now consider s2 n = 1 + 2^2 + 3^2 + ... + n^2.
-/

def s2 (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => (s2 n) + (n + 1) ^ 2

lemma s2_zero : s2 0 = 0 := by rfl

lemma s2_succ (n : ℕ) : s2 (n + 1) = s2 n + (n + 1) ^ 2 := by rfl


example (n : ℕ) : s2 n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · -- base case: s2 0 = ...
    rw [s2_zero]
    numbers
  · -- inductive step: s2 (k + 1) = ...
    rw [s2_succ]
    rw [IH]
    ring

/-
  We now prove the beautiful formula s3 n  = (s1 n) ^ 2.
  E.g. 2025 = 1^3 + 2^3 + ... + 9^3 = (1 + 2 + ... + 9)^2
-/

def s3 (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => (s3 n) + (n + 1) ^ 3

lemma s3_zero : s3 0 = 0 := by rfl

lemma s3_succ (n : ℕ) : s3 (n + 1) = s3 n + (n + 1) ^ 3 := by rfl

example (n : ℕ) : s3 n = (s1 n) ^ 2 := by
  simple_induction n with k IH
  · -- base case: s3 0 = (s1 0) ^ 2
    rw [s1_zero, s3_zero]
    numbers
  · -- inductive step: s3 (k + 1) = (s1 (k + 1)) ^ 2
    -- note: you will need to use the lemma `s1_formula` here
    rw [s3_succ, s1_succ]
    rw [IH]
    rw [s1_formula k]
    ring



/-
  Let us prove that s2 n ≥ n^3 / 3.
-/


example (n : ℕ) : 3 * s2 n ≥ n ^ 3 := by
  simple_induction n with k IH
  · -- base case: s2 0 ≥ 0
    rw [s2_zero]
    numbers
  · -- inductive step: s2 (k + 1) ≥ (k + 1) ^ 3 / 3
    rw [s2_succ]
    calc
      3 * (s2 k + (↑k + 1) ^ 2) = 3 * s2 k + 3 * (↑k + 1) ^ 2 := by ring
      _ ≥ ↑k ^ 3 + 3 * (↑k + 1) ^ 2 := by rel [IH]
      _ = ↑k ^ 3 + 3 * ↑k ^ 2 + 3 * ↑k + 1 + (3 * ↑k + 2) := by ring
      _ ≥ ↑k ^ 3 + 3 * ↑k ^ 2 + 3 * ↑k + 1 := by extra
      _ = (↑k + 1) ^ 3 := by ring
