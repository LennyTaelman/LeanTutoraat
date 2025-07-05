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
  Natural factorial
-/

def nat_fac (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * nat_fac n

lemma nat_fac_zero : nat_fac 0 = 1 := by rfl

lemma nat_fac_succ (n : ℕ) : nat_fac (n + 1) = (n + 1) * nat_fac n := by rfl

lemma fac_eq_nat_fac (n : ℕ) : fac n = nat_fac n := by
  simple_induction n with n IH
  · rw [fac_zero]
    rw [nat_fac_zero]
    numbers
  · rw [fac_succ]
    rw [nat_fac_succ]
    rw [IH]
    norm_cast -- should be ring?



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


lemma s_lt_next (n : ℕ) : s n < s (n + 1) := by
  rw [s_succ]
  addarith [a_pos n]

lemma s_monotone (n : ℕ) (m : ℕ) (hm : m > n) : s n < s m := by
  induction_from_starting_point m, hm with k hk IH
  · exact s_lt_next n
  · calc
    _ < s k := by rel [IH]
    _ < s (k + 1) := by rel [s_lt_next k]

lemma s_nonneg (n : ℕ) : s n ≥ 0 := by
  simple_induction n with n IH
  · rw [s_zero]
  · rw [s_succ]
    addarith [IH, a_pos n]

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







lemma s_under_geometric (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    s (n + k) - s n ≤ (a n) * ∑ i in range k, c ^ i := by
  simple_induction k with k IH
  · -- base case
    rw [sum_range_zero]
    rw [add_zero, sub_self, mul_zero] -- TODO: make this a tactic?
  · -- inductive step
    calc
      _ = s ((n + k) + 1) - s n := by ring
      _ = s (n + k) + a (n + k) - s n := by rw [s_succ]
      _ = (s (n + k) - s n) + a (n + k) := by ring
      _ ≤ (a n) * ∑ i in range k, c ^ i + a (n + k) := by rel [IH]
      _ ≤ (a n) * ∑ i in range k, c ^ i + c ^ k * a n := by rel [a_bound n k hn]
      _ = (a n) * ∑ i in range k, c ^ i + c ^ k * (a n) := by rw [a_def]
      _ = (a n) * (∑ i in range k, c ^ i + c ^ k) := by ring
      _ = (a n) * (∑ i in range (k + 1), c ^ i) := by rw [sum_range_succ]


theorem key_bound (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    s (n + k) - s n ≤ (a n) * 2 := by
  have h : a n > 0 := a_pos n
  calc
    _ ≤ (a n) * ∑ i in range k, c ^ i := by rel [s_under_geometric n k hn]
    _ ≤ (a n) * 2 := by rel [geometric_sum_lt_2 k]

lemma s_bounded' (n : ℕ) : s (n + 1) ≤ 3 := by
  have h : 1 ≥ 1 := by numbers
  calc
    _ = (s (1 + n) - s 1) + s 1 := by ring
    _ ≤ (a 1) * 2 + s 1 := by rel [key_bound 1 n h]
    _ = 1 * 2 + 1 := by rw [a_one, s_one]
    _ = 3 := by numbers

-- trick: can use `simple_induction` to distinguish
-- between n = 0 and n = k + 1, while ignoring the induction hypothesis ;-)
lemma s_bounded (n : ℕ) : s n ≤ 3 := by
  simple_induction n with k IH
  · rw [s_zero]
    numbers
  · apply s_bounded'




/-
  The next part shows that the sequence s n is Cauchy, defines e : ℝ to be its
  limit, and establishes two key lemma:
  - s n < e for all n
  - for all ε > 0, ∃ N : ℕ, ∀ n ≥ N, e < s n + ε
  The proofs have been pre-filled, since they require working closely with the
  definitions of ℝ, "Cauchy" and "limit" as implemented in Mathlib.

  However, the two key lemmas IMPLY that "e" agrees with the real number e,
  so that you don't need to take this on faith.

  In the rest of this worksheet, you don't use the definition of e, but
  the two key lemmas.
-/


theorem s_cauchy : IsCauSeq abs s := by
  have h : ∀ n, n ≥ 0 → |s n| ≤ 3 := by
    intro n _
    rw [abs_of_nonneg]
    apply s_bounded
    apply s_nonneg
  apply isCauSeq_of_mono_bounded
  · exact h
  · intro n hn
    rel [s_lt_next n]

def e : ℝ := CauSeq.lim ⟨fun n => s n, s_cauchy⟩

lemma e_below_3 : e ≤ 3 := by
  unfold e
  sorry

lemma s_below_e (n : ℕ) : s n < e := by
  have h : CauSeq.const abs (s (n+1)) ≤ ⟨fun n => s n, s_cauchy⟩ := by
    apply CauSeq.le_of_exists
    use n+1
    intro j hj
    dsimp
    by_cases h2 : j = n + 1
    · rw [h2]
    · have h3 : j > n+1 := by exact Ne.lt_of_le' h2 hj
      rel [s_monotone (n + 1) j h3]
  have h2 : s n < s (n+1) := by rel [s_lt_next n]
  calc
    _ < s (n+1) := by rel [h2]
    _ ≤ e := by exact CauSeq.le_lim h

lemma s_tends_to_e : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - e| < ε := by
  intro ε hε
  sorry


/-
  We will now prove that e is irrational. Consider the tail

  t n = e - s n = 1 / n! + 1 / (n+1)! + ...

  By the key bound, we have t n ≤ 2 * 1 / n!, so
  n! * t (n + 1) < 1 for n > 1

  Note that n! * s (n + 1) is an integer.

  Now if e is rational, then n! * e is an integer for n big enough

  But then n! * t (n + 1) is an integer/

  This is a contradiction with the fact that n! * t (n + 1) < 1.

-/

def t (n : ℕ) := e - s n

lemma t_def (n : ℕ) : t n = e - s n := by rfl

lemma t_pos (n : ℕ) : 0 < t n := by
  rw [t_def]
  addarith [s_below_e n]


lemma fac_div_integral (q : ℕ) (hq : q > 0) : (fac q) = q * nat_fac (q - 1) := by
  have h : (q - 1) + 1 = q := by exact Nat.sub_add_cancel hq
  rw [← h]
  rw [fac_succ]
  rw [fac_eq_nat_fac]
  norm_cast -- should be ring or numbers


lemma e_rational_factorial :
    (∃ p q : ℕ, q > 0 ∧ e = p / q) → (∃ n > 1, ∃ m : ℕ, (fac n) * e = m) := by
  intro h
  obtain ⟨p, q, hq, he⟩ := h
  use q + 1
  constructor
  · addarith [hq]
  · rw [he]
    rw [fac_succ]
    use nat_fac (q - 1) * p * (q + 1)
    rw [fac_div_integral]
    norm_cast
    field_simp
    ring
    exact hq




  theorem e_irrational : ¬ ∃ p q : ℕ, q > 0 ∧ e = p / q := by
  intro h
  obtain ⟨n, hn, m, hm⟩ := e_rational_factorial h


  sorry

#print axioms e_irrational
