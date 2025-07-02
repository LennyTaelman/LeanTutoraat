/- Copyright (c) Lenny Taelman, 2025.  All rights reserved. -/
import Mathlib
import Library.Basic

math2001_init

open Nat Finset Real BigOperators
noncomputable section


/-
  In this worksheet, we will prove that e is irrational. This is intended as a
  group project, where participants can work on different parts of the proof
  in parallel.
-/


/-
  The factorial function. Rather than using its definition, you should
  use the two defining lemmas :
  - fac_zero : fac 0 = 1
  - fac_succ : fac (n + 1) = (n + 1) * fac n
-/

def fac (n : ℕ) : ℝ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * fac n

lemma fac_zero : fac 0 = 1 := by rfl

lemma fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by rfl


/-
  Prove some basic facts about the factorial function.
-/

lemma fac_one : fac 1 = 1 := by rw [fac_succ]; rw [fac_zero]; numbers

lemma fac_two : fac 2 = 2 := by rw [fac_succ]; rw [fac_one]; numbers

-- lemma fac_ne_zero (n : ℕ) : fac n ≠ 0 := by
--   simple_induction n with n IH
--   · rw [fac_zero]
--     numbers
--   · rw [fac_succ]
--     apply mul_ne_zero
--     · addarith []
--     · exact IH

lemma fac_ge_one (n : ℕ) : fac n ≥ 1 := by
  simple_induction n with n IH
  · rw [fac_zero]
  · have h : (n : ℝ) + 1 ≥ 1 := by addarith []
    calc fac (n + 1) = (n + 1) * fac n := by rw [fac_succ]
      _ ≥ 1 * fac n := by rel [h]
      _ ≥ 1 := by addarith [IH]

lemma fac_gt_zero (n : ℕ) : fac n > 0 := by
  calc fac n ≥ 1 := by apply fac_ge_one
    _ > 0 := by numbers

lemma fac_ne_zero (n : ℕ) : fac n ≠ 0 := by
  addarith [fac_gt_zero n]


/-
  The key lower bound on the factorial function
-/

theorem fac_bound (n : ℕ) (k : ℕ) (hn : n > 0) :
    fac (n + k) ≥ 2 ^ k * fac n := by
  simple_induction k with k IH
  · -- base case
    calc fac (n + 0) = fac n := by ring
      _ ≥ 1 * fac n := by addarith []
  · -- inductive step
    have h : (n : ℝ) + (k : ℝ) + 1 ≥ 2 := by norm_cast; addarith [hn]
    have h2 : (2 : ℝ) ^ k > 0 := by positivity
    have h3 : 2 ^ k * fac n > 0 := by
      exact mul_pos h2 (fac_gt_zero n)
    calc fac (n + (k + 1)) = fac (n + k + 1) := by ring
      _ = (n + k + 1) * fac (n + k) := by rw [fac_succ]; norm_cast
      _ ≥ (n + k + 1) * (2 ^ k * fac n) := by rel [IH]
      _ ≥ 2 * (2 ^ k * fac n) := by rel [h]
      _ = 2 ^ (k + 1) * fac n := by ring


lemma self_div_eq_0 (x : ℝ) (h : x > 0) : x / x = 1 := by
  field_simp

lemma fac_div_fac_integral (n : ℕ) (m : ℕ) (h : n ≥ m) :
    ∃ N : ℤ, fac n * (fac m)⁻¹ = N := by
  induction_from_starting_point n, h with k hk IH
  · use 1; sorry
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
  apply sub_lt_self
  positivity

/-
  De rij a_n = 1 / fac n
-/

-- type the exponent -1 using \inv

def a (n : ℕ) := (fac n)⁻¹

lemma a_def (n : ℕ) : a n = (fac n)⁻¹ := by rfl

lemma a_zero : a 0 = 1 := by rw [a_def, fac_zero]; numbers

lemma a_one : a 1 = 1 := by rw [a_def, fac_one]; numbers

lemma a_mul_fac_eq_one (n : ℕ) : a n * fac n = 1 := by
  rw [a_def]
  apply inv_mul_cancel
  exact fac_ne_zero n

lemma a_pos (n : ℕ) : a n > 0 := by
  apply inv_pos.mpr -- TODO: find better lemma name for this
  exact fac_gt_zero n


/-
  De partiele sommen s_n = ∑_{i=0}^{n-1} a_i van de reeks ∑_{i=0}^{∞} a_i

  s n = a 0 + a 1 + ... + a (n-1)   (n termen)
-/

def s (n : ℕ) := ∑ i in range n, a i

lemma s_def (n : ℕ) : s n = ∑ i in range n, a i := by rfl

lemma s_zero : s 0 = 0 := by rfl

lemma s_succ (n : ℕ) : s (n + 1) = s n + a n := by
  rw [s_def]
  rw [sum_range_succ]
  rw [s_def]

lemma s_one : s 1 = 1 := by rw [s_succ, s_zero, a_zero]; numbers


lemma s_monotone (n : ℕ) : s n < s (n + 1) := by
  rw [s_succ]
  addarith [a_pos n]




lemma factorial_s_succ (n : ℕ) :
    (fac (n + 1)) * s (n + 2) = (n + 1) * (fac n) * s (n + 1) + 1 := by
  rw [s_succ]

  rw [fac_succ]
  sorry

lemma a_integrality (n : ℕ) : ∃ m : ℕ, (fac n) * s (n + 1) = m := by
  simple_induction n with n IH
  · use 1
    rw [s_succ]
    rw [fac_zero]
    rw [s_zero, a_zero]
    numbers
  · obtain ⟨m, hm⟩ := IH
    use (n + 1) * m + 1
    rw [factorial_s_succ, mul_assoc]
    rw [hm]
    norm_cast



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

lemma s_below_e (n : ℕ) : s n < e := by sorry

theorem s_to_e : ∀ ε > 0, ∃ N : ℕ, e < s N + ε := by sorry



/-
  We will now prove that e is irrational. Assume e = p / q with p, q ∈ ℕ and q > 0.

  Consider the real number x = q! * (e - a (q + 1)).

  Note: x = q! * (1 / (q + 1)! + 1 / (q + 2)! + ... )

-/



variable (p : ℕ) (q : ℕ) (hq : q > 0) (hrat : q * e = p)

def x := q ! * (e - s (q + 1))


lemma x_integrality : ∃ N : ℤ, x = N := by
  obtain ⟨m, hm⟩ := a_integrality q
  use (q - 1)! * p - m
  -- warning: this is Nat subtraction, so need to explicitly use hq somewher

  sorry
