/- Copyright (c) Lenny Taelman, 2025.  All rights reserved. -/
import Mathlib
import Library.Basic

math2001_init

open Nat Finset Real BigOperators
noncomputable section


/-
  De faculteit

  lemma factorial_succ (n : ℕ) : (n + 1) ! = (n + 1) * n ! := by
-/

#check Nat.factorial_succ



/-
  Integraliteit:
    IsIntegral (x : ℝ) : Prop
    gesloten onder +, 0, 1, -, *
    x>0, x integral => x ≥ 1

  TODO: move to import file
-/




/-
  Propositie: (n + k)! ≥ 2 ^ k * n!
-/


lemma afschatting_faculteit (n : ℕ) (k : ℕ) (h_n : n > 0) :
    (n + k) ! ≥ 2 ^ k * n ! := by
  simple_induction k with k IH
  · -- base case
    calc (n + 0) ! = n ! := by ring
      _ = 2 ^ 0 * n ! := by ring
      _ ≥ 1 * n ! := by extra
  · -- inductive step
    have h : n + k + 1 ≥ 2 := by addarith [h_n]
    calc (n + (k + 1)) ! = ((n + k) + 1) ! := by ring
      _ = (n + k + 1) * (n + k) ! := by rw [factorial_succ]
      _ ≥ (n + k + 1) * (2 ^ k * n !) := by rel [IH]
      _ ≥ 2 * (2 ^ k * n !) := by rel [h]
      _ = 2 ^ (k + 1) * n ! := by ring

-- looks the same, but this is an inequality in ℝ
lemma afschatting_reel (n : ℕ) (k : ℕ) (h_n : n > 0) :
    ((n + k) ! : ℝ) ≥ 2 ^ k * n ! := by
  norm_cast -- this reduces the goal to the same inequality in ℕ
  apply afschatting_faculteit n k h_n



/-
  Propositie: ∑_{i=0}^{k-1} 1 / (2 ^ i : ℝ) ≤ 2
-/

#check Finset.sum

lemma geometric_sum (k : ℕ) : ∑ i in range k, 1 / (2 : ℝ) ^ i = 2 - 2 / (2 : ℝ) ^ k := by
  simple_induction k with k IH
  · -- base case
    ring
  · -- inductive step
    rw [Finset.sum_range_succ]
    rw [IH]
    ring

lemma geometric_sum_lt_2 (k : ℕ) : ∑ i in range k, 1 / (2 : ℝ) ^ i < 2 := by
  rw [geometric_sum]
  sorry

/-
  De rij a_n die naar e convergeert. De termen zijn:

  a n = 1/0! + 1/1! + ... + 1/(n-1)!

  Note that a n consists of n terms
-/

def a (n : ℕ) := ∑ i in range n, 1 / (i ! : ℝ)

lemma a0 : a 0 = 0 := by rfl

lemma a1 : a 1 = 1 := by unfold a; norm_num

lemma a2 : a 2 = 2 := by unfold a; unfold Finset.sum; norm_num

lemma a3 : a 3 = 5/2 := by unfold a; unfold Finset.sum; norm_num

example (x y : ℝ) (h : 0 ≤ y) : x ≤ x + y := by exact le_add_of_nonneg_right h

lemma a_monotone (n : ℕ) : a n ≤ a (n + 1) := by
  unfold a
  rw [sum_range_succ]
  apply le_add_of_nonneg_right
  positivity


/-
  The next part introduces the number e and establishes that a n converges to e.
  In this worksheet, we will take this as a known block box, i.e. assume
  others have already proved it. Since Lean has checked the statement, we
  can trust it.

  Alternative interpretation: use the statements below as an (implicit)
  definition of the number e. Key facts:
  - e is a real number
  - a n < e
  - a n ≤ a (n+1)
  - for all ε > 0, ∃ N : ℕ, e < a N + ε
  Verify for yourself that these uniquely determine e.
-/


def e := exp 1

lemma a_below_e (n : ℕ) : a n < e := by sorry

theorem a_to_e : ∀ ε > 0, ∃ N : ℕ, e < a N + ε := by sorry


#min_imports
