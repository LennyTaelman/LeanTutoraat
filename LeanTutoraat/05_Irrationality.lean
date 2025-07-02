/- Copyright (c) Lenny Taelman, 2025.  All rights reserved. -/
import Mathlib
import Library.Basic

-- NOTE: this also establishes a basic simp tactic
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

lemma aux (n : ℕ) (k : ℕ) :
    0 < 2 ^ k * fac n := by
  apply mul_pos
  · positivity
  · exact fac_gt_zero n


theorem fac_bound (n : ℕ) (k : ℕ) (hn : n > 0) :
    fac (n + k) ≥ 2 ^ k * fac n := by
  simple_induction k with k IH
  · -- base case
    calc fac (n + 0) = fac n := by ring
      _ ≥ 1 * fac n := by addarith []
  · -- inductive step
    have h : (n : ℝ) + (k : ℝ) + 1 ≥ 2 := by norm_cast; addarith [hn]
    have h2 : (2 : ℝ) ^ k > 0 := by positivity
    have h3 : 2 ^ k * fac n > 0 := by exact aux n k
    calc fac (n + (k + 1)) = fac (n + k + 1) := by ring
      _ = (n + k + 1) * fac (n + k) := by rw [fac_succ]; norm_cast
      _ ≥ (n + k + 1) * (2 ^ k * fac n) := by rel [IH]
      _ ≥ 2 * (2 ^ k * fac n) := by rel [h]
      _ = 2 ^ (k + 1) * fac n := by ring


/-
  Propositie: ∑_{i=0}^{k-1} 1 / (2 ^ i : ℝ) ≤ 2
-/

def c : ℝ := 1 / (2 : ℝ)

lemma c_def : c = 1 / (2 : ℝ) := by rfl

lemma c_pos : c > 0 := by rw [c_def]; positivity


lemma geometric_sum (k : ℕ) : ∑ i in range k, c ^ i = 2 - 2 * c ^ k := by
  simple_induction k with k IH
  · -- base case
    rw [sum_range_zero]
    ring
  · -- inductive step
    rw [Finset.sum_range_succ]
    rw [IH]
    rw [c_def]
    ring

lemma geometric_sum_lt_2 (k : ℕ) : ∑ i in range k, c ^ i < 2 := by
  rw [geometric_sum]
  simp
  rw [c_def]
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

lemma a_pos (n : ℕ) : 0 < a n  := by
  rw [a_def]
  -- TODO: find better tactic to do this (addarith? variation)
  rw [inv_pos]
  exact fac_gt_zero n

lemma a_succ (n : ℕ) : a (n + 1) = ((n : ℝ) + 1)⁻¹ *  a n  := by
  rw [a_def]
  rw [fac_succ]
  rw [a_def]
  simp only [mul_inv_rev]
  ring

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

/-
  Establish that n ! * s (n + 1) is an integer.
-/


lemma factorial_s_succ (n : ℕ) :
    (fac (n + 1)) * s (n + 2) = (n + 1) * (fac n) * s (n + 1) + 1 := by
  calc
    _ = fac (n + 1) * ( s (n + 1) + a (n + 1)) := by rw [s_succ]
    _ = fac (n + 1) * s (n + 1) + fac (n + 1) * a (n + 1) := by ring
    _ = (n + 1) * fac n * s (n + 1) + fac (n + 1) * a (n + 1) := by rw [fac_succ]
    _ = (n + 1) * fac n * s (n + 1) + a (n + 1) * fac (n + 1) := by ring
    _ = (n + 1) * fac n * s (n + 1) + 1 := by rw [a_mul_fac_eq_one]


lemma s_integrality (n : ℕ) : ∃ m : ℕ, (fac n) * s (n + 1) = m := by
  simple_induction n with n IH
  · use 1
    rw [s_succ]
    rw [fac_zero]
    rw [s_zero, a_zero]
    numbers
  · obtain ⟨m, hm⟩ := IH -- obtain an m from the ∃ in the inductive hypothesis
    use (n + 1) * m + 1
    rw [factorial_s_succ, mul_assoc]
    rw [hm]
    norm_cast -- TODO: user will expect 'ring' here


/-
  Key inequality for s n
-/

-- alternative: use fac_bound


-- TODO: really need to practice a bit with inverses and inequalities
-- this is a MESS now







lemma n_plus_one_inv_le_c (n : ℕ) (hn : n ≥ 1) : ((n : ℝ) + 1)⁻¹ ≤ c := by
  rw [c_def]
  apply inv_le_of_inv_le
  · numbers
  · norm_num; norm_cast; addarith [hn] -- TODO: import norm_cast into addarith?


lemma a_halving (n : ℕ) (hn : n ≥ 1) : a (n + 1) ≤ c * a n  := by
  have h : a n > 0 := a_pos n
  calc
    _ = ((n:ℝ) + 1)⁻¹ * a n := by rw [a_succ]
    _ ≤ c * a n := by rel [n_plus_one_inv_le_c n hn]


lemma a_bound (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    a (n + k) ≤  c^ k * (a n)  := by
  have h : c > 0 := by exact c_pos
  simple_induction k with k IH
  · -- base case
    simp
    rfl
  · -- inductive step
    calc
      _ = a ((n + k) + 1) := by ring
      _ ≤ c * a (n + k)  := by apply a_halving; addarith [hn]
      _ ≤ c * (c ^ k * a n) := by rel [IH]
      _ = c ^ (k + 1) * a n := by ring







lemma key_bound (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    s (n + k) - s n ≤ (fac n)⁻¹ * ∑ i in range k, c ^ i := by
  simple_induction k with k IH
  · -- base case
    rw [sum_range_zero]
    rw [add_zero, sub_self, mul_zero] -- TODO: make this a tactic?
  · -- inductive step
    calc
      _ = s ((n + k) + 1) - s n := by ring
      _ = s (n + k) + a (n + k) - s n := by rw [s_succ]
      _ = (s (n + k) - s n) + a (n + k) := by ring
      _ ≤ (fac n)⁻¹ * ∑ i in range k, c ^ i + a (n + k) := by rel [IH]
      _ ≤ (fac n)⁻¹ * ∑ i in range k, c ^ i + c ^ k * a n := by rel [a_bound n k hn]
      _ = (fac n)⁻¹ * ∑ i in range k, c ^ i + c ^ k * (fac n)⁻¹ := by rw [a_def]
      _ = (fac n)⁻¹ * (∑ i in range k, c ^ i + c ^ k) := by ring
      _ = (fac n)⁻¹ * (∑ i in range (k + 1), c ^ i) := by rw [sum_range_succ]





/-
  The next part introduces the number e and establishes that a n converges to e.
  In this worksheet, we will take this as a known block box, i.e. assume
  others have already proved it. Since Lean has checked the statement, we
  can trust it.

  Alternative interpretation: use the statements below as an (implicit)
  definition of the number e. Key facts:
  - e is a real number
  - s n < e
  - for all ε > 0, ∃ N : ℕ, ∀ n ≥ N, e < s n + ε
  Verify for yourself that these uniquely determine e.

  TODO: move these to an imported file, just mention the defining lemmas here
  No! Cannot do this, since we need the definition of s n here.
-/


def e := exp 1

lemma s_below_e (n : ℕ) : s n < e := by sorry

theorem s_to_e : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, e < s n + ε := by sorry



/-
  We will now prove that e is irrational. Consider the tail

  t n = e - s n = 1 / n! + 1 / (n+1)! + ...

  By the key bound, we have t n ≤ 2 * 1 / n!, so
  (n-1)! * t n < 1 for n > 2

  Note that (n-1)! * s n is an integer, so (n-1)! * t n is also an integer.

  Now if e is rational, then (n-1)! * e is an integer for n big enough

  But then (n-1)! * t n is an integer, and (n-1)! * t n < 1

  This is a contradiction.

-/

def t (n : ℕ) := e - s n

lemma t_def (n : ℕ) : t n = e - s n := by rfl

lemma t_pos (n : ℕ) : 0 < t n := by
  rw [t_def]
  addarith [s_below_e n]
