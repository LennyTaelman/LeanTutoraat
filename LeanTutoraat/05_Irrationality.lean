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

def fac (n : ℕ) : ℝ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * fac n

lemma fac_zero : fac 0 = 1 := by rfl

lemma fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by rfl

lemma fac_ge_one (n : ℕ) : fac n ≥ 1 := by
  simple_induction n with n IH
  · -- base case
    rw [fac_zero]
  · -- inductive step
    have h : (n : ℝ) + 1 ≥ 1 := by addarith []
    calc fac (n + 1) = (n + 1) * fac n := by rw [fac_succ]
      _ ≥ 1 * fac n := by rel [h]
      _ ≥ 1 := by addarith [IH]

lemma fac_gt_zero (n : ℕ) : fac n > 0 := by
  calc fac n ≥ 1 := by apply fac_ge_one
    _ > 0 := by numbers


lemma fac_bound (n : ℕ) (k : ℕ) (hn : n > 0) :
    fac (n + k) ≥ 2 ^ k * fac n := by
  simple_induction k with k IH
  · -- base case
    calc fac (n + 0) = fac n := by ring
      _ ≥ 1 * fac n := by addarith []
  · -- inductive step
    have h : (n : ℝ) + (k : ℝ) + 1 ≥ 2 := by norm_cast; addarith [hn]
    have h2 : 2 ^ k * fac n > 0 := by sorry
    calc fac (n + (k + 1)) = fac (n + k + 1) := by ring
      _ = (n + k + 1) * fac (n + k) := by rw [fac_succ]; norm_cast
      _ ≥ (n + k + 1) * (2 ^ k * fac n) := by rel [IH]
      _ ≥ 2 * (2 ^ k * fac n) := by rel [h]
      _ = 2 ^ (k + 1) * fac n := by ring


lemma self_div_eq_0 (x : ℝ) (h : x > 0) : x / x = 1 := by
  field_simp

lemma fac_div_fac_integral (n : ℕ) (m : ℕ) (h : n ≥ m) :
    ∃ N : ℤ, fac n / fac m = N := by
  induction_from_starting_point n, h with k hk IH
  · use 1; norm_cast; apply self_div_eq_0; exact fac_gt_zero m
  · obtain ⟨N, hN⟩ := IH
    use N * (k + 1)
    rw [fac_succ]
    simp_all
    rw [← hN]
    field_simp
    ring



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

def a (n : ℕ) := ∑ i in range n, 1 / fac i

lemma a0 : a 0 = 0 := by rfl

lemma a1 : a 1 = 1 := by unfold a; norm_num; exact fac_zero


lemma le_add_pos  (x y : ℝ) (h : 0 ≤ y) : x ≤ x + y := by
  addarith [h]

lemma a_succ (n : ℕ) : a (n + 1) = a n + 1 / (n ! : ℝ) := by
  unfold a
  rw [sum_range_succ]


lemma a_monotone (n : ℕ) : a n ≤ a (n + 1) := by
  unfold a
  rw [sum_range_succ]
  have h : 0 ≤ 1 / (n ! : ℝ) := by positivity
  apply le_add_pos
  exact h


lemma factorial_a_succ (n : ℕ) :
    (n + 1)! * a (n + 2) = (n + 1) * n ! * a (n + 1) + 1 := by
  rw [a_succ]
  rw [factorial_succ]
  field_simp
  ring

lemma a_integrality (n : ℕ) : ∃ m : ℕ, n ! * a (n + 1) = m := by
  simple_induction n with n IH
  · -- base case
    use 1
    rw [a]
    norm_num
  · -- inductive step
    obtain ⟨m, hm⟩ := IH
    use (n + 1) * m + 1
    rw [factorial_a_succ]
    push_cast
    rw [← hm]
    ring



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


/-
  We will now prove that e is irrational. Assume e = p / q with p, q ∈ ℕ and q > 0.

  Consider the real number x = q! * (e - a (q + 1)).

  Note: x = q! * (1 / (q + 1)! + 1 / (q + 2)! + ... )

-/



variable (p : ℕ) (q : ℕ) (hq : q > 0) (hrat : q * e = p)

def x := q ! * (e - a (q + 1))


lemma x_integrality : ∃ N : ℤ, x = N := by
  obtain ⟨m, hm⟩ := a_integrality q
  use (q - 1)! * p - m
  -- warning: this is Nat subtraction, so need to explicitly use hq somewher

  sorry
