/- Copyright (c) Lenny Taelman, 2025.  All rights reserved. -/
import Mathlib
import Library.Basic

-- NOTE: this now also establishes a basic simp tactic
math2001_init

open Nat Finset Real BigOperators
noncomputable section



/-
  In this worksheet, we will prove that e is irrational. This is intended as a
  larger group project, where participants can work on different parts of the proof
  in parallel.

  Below is a detailed skeleton proof, with the argument already split into many
  smaller lemmas. The class will work on those in parallel, replacing all the
  `sorry`s with actual proofs, until the proof of the main theorem
  no longer uses any `sorry`.
-/


/-
  The factorial function. Rather than using its definition, you should
  use the two defining lemmas :
  - fac_zero : fac 0 = 1
  - fac_succ : fac (n + 1) = (n + 1) * fac n
-/

def fac (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * fac n

lemma fac_zero : fac 0 = 1 := by rfl

lemma fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by rfl


/-
  Prove some basic facts about the factorial function.
-/

lemma fac_one : fac 1 = 1 := by rw [fac_succ]; rw [fac_zero]

lemma fac_two : fac 2 = 2 := by rw [fac_succ]; rw [fac_one]

lemma fac_three : fac 3 = 6 := by rw [fac_succ]; rw [fac_two]

lemma fac_ge_one (n : ℕ) : fac n ≥ 1 := by
  simple_induction n with n IH
  · rw [fac_zero]
  · have h : n + 1 ≥ 1 := by extra
    calc
      fac (n + 1) = (n + 1) * fac n := by rw [fac_succ]
      _ ≥ 1 * fac n := by rel [h]
      _ = fac n := by ring
      _ ≥ 1 := by apply IH

lemma fac_monotone (n : ℕ) (m : ℕ) (hm : m ≥ n) : fac m ≥ fac n := by
  induction_from_starting_point m, hm with k hk IH
  · extra
  · have h : k + 1 ≥ 1 := by extra
    calc
      fac (k + 1) = (k + 1) * fac k := by rw [fac_succ]
      _ ≥ 1 * fac k := by rel [h]
      _ = fac k := by ring
      _ ≥ fac n := by rel [IH]

lemma fac_pos (n : ℕ) : fac n > 0 := by
  calc fac n ≥ 1 := by apply fac_ge_one
    _ > 0 := by numbers

lemma fac_ne_zero (n : ℕ) : fac n ≠ 0 := by
  have h : fac n > 0 := by apply fac_pos
  positivity

lemma fac_ge_two (n : ℕ) (hn : n ≥ 2) : fac n ≥ 2 := by
  calc fac n ≥ fac 2 := fac_monotone 2 n hn
    _ = 2 := by rw [fac_two]


/-
  The key lower bound on the factorial function
-/

lemma aux (n : ℕ) (k : ℕ) : 0 < 2 ^ k * fac n := by
  have h : fac n > 0 := by apply fac_pos
  positivity

/-
  The following is the key inequality in the proof of irrationality of e.
  I recommend you write out the proof in detail on paper first.
-/
theorem fac_bound (n : ℕ) (k : ℕ) (hn : n > 0) :
    fac (n + k) ≥ 2 ^ k * fac n := by
  simple_induction k with k IH
  · -- base case
    calc fac (n + 0) = 1 * fac n := by ring
      _ ≥ 1 * fac n := by extra
  · -- inductive step
    have h1 : n + k + 1 ≥ 2 := by addarith [hn]
    have h2 : fac n > 0 := by apply fac_pos
    calc fac (n + (k + 1)) = fac (n + k + 1) := by ring
      _ = (n + k + 1) * fac (n + k) := by rw [fac_succ]
      _ ≥ (n + k + 1) * (2 ^ k * fac n) := by rel [IH]
      _ ≥ 2 * (2 ^ k * fac n) := by rel [h1]
      _ = 2 ^ (k + 1) * fac n := by ring


/-
  Propositie: ∑_{i=0}^{k-1} 1 / (2 ^ i : ℝ) ≤ 2
-/


def c (k : ℕ) : ℝ :=
  match k with
  | 0 => 1
  | k + 1 => c k / 2

lemma c_zero : c 0 = 1 := by rfl

lemma c_succ (k : ℕ) : c (k + 1) = c k / 2 := by rfl

lemma c_pos (k : ℕ) : c k > 0 := by
  simple_induction k with k IH
  · rw [c_zero]
    positivity
  · rw [c_succ]
    positivity


def g (k : ℕ) : ℝ :=
  match k with
  | 0 => 0
  | k + 1 => g k + c k

lemma g_zero : g 0 = 0 := by rfl

lemma g_succ (k : ℕ) : g (k + 1) = g k + c k := by rfl


lemma geometric_sum (k : ℕ) : g k = 2 - 2 * c k := by
  simple_induction k with k IH
  · rw [g_zero, c_zero]
    numbers
  · -- inductive step
    rw [g_succ, c_succ]
    rw [IH]
    ring

lemma geometric_sum_lt_2 (k : ℕ) : g k < 2 := by
  rw [geometric_sum]
  have h : c k > 0 := by apply c_pos
  extra



/-
  The sequence a_n = 1 / fac n
-/

-- def a (n : ℕ) : ℝ := (fac n : ℝ)⁻¹

def a (n : ℕ) : ℝ :=
  match n with
  | 0 => 1
  | n + 1 => a n / (n + 1)

lemma a_zero : a 0 = 1 := by rfl

lemma a_succ (n : ℕ) : a (n + 1) = a n / (n + 1) := by rfl

lemma a_one : a 1 = 1 := by rw [a_succ, a_zero]; numbers

lemma a_two : a 2 = 1 / 2 := by rw [a_succ, a_one]; numbers

lemma a_three : a 3 = 1 / 6 := by rw [a_succ, a_two]; numbers

lemma a_pos (n : ℕ) : 0 < a n  := by
  simple_induction n with n IH
  · rw [a_zero]
    positivity
  · rw [a_succ]
    positivity

lemma a_succ' (n : ℕ) : (n + 1) * a (n + 1) = a n := by
  rw [a_succ]
  field_simp -- bottleneck
  ring

lemma fac_mul_a_eq_one (n : ℕ) : fac n * a n = 1 := by
  simple_induction n with n IH
  · rw [a_zero, fac_zero]
    numbers
  · calc
      fac (n + 1) * a (n + 1) = (n + 1) * fac n * a (n + 1) := by rw [fac_succ]; push_cast; ring
      _ = fac n * ((n + 1) * (a (n + 1))) := by ring
      _ = fac n * a n := by rw [a_succ']
      _ = 1 := by rw [IH]

lemma a_le_1 (n : ℕ) : a n ≤ 1 := by
  simple_induction n with n IH
  · rw [a_zero]
  · rw [a_succ]
    have h : ↑n + 1 ≥ 1 := by extra
    calc
      a n / (n + 1) ≤ a n := by sorry
      _ ≤ 1 := by apply IH


/-
  Integrality
-/

def isInt (a : ℝ) : Prop := ∃ N : ℤ, a = N

lemma isInt_zero : isInt 0 := by use 0; numbers

lemma isInt_one : isInt 1 := by use 1; numbers

lemma isInt_nat (n : ℕ) : isInt (n : ℝ) := by use n; rfl

lemma isInt_add (a b : ℝ) (ha : isInt a) (hb : isInt b) : isInt (a + b) := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := hb
  use N + M
  rw [hN, hM]
  push_cast; ring

lemma isInt_mul (a b : ℝ) (ha : isInt a) (hb : isInt b) : isInt (a * b) := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := hb
  use N * M
  rw [hN, hM]
  push_cast; ring

lemma isInt_nat_mul (a : ℝ) (h : isInt a) (n : ℕ) : isInt (n * a) := by
  obtain ⟨N, hN⟩ := h
  use n * N
  rw [hN]
  push_cast; ring

-- m! * a n is integral as soon as m ≥ n

lemma isInt_fac_mul_a (n m : ℕ) (h : n ≤ m) : isInt (fac m * a n) := by
  induction_from_starting_point m, h with k hk IH
  · rw [fac_mul_a_eq_one]
    apply isInt_one
  · -- bottleneck: make clear that k+1 is a nat!
    -- bottleneck: instinct should be to do rw [fac_succ] FIRST!
    have h2 : fac (k + 1) * a n = (k + 1 : ℕ) * (fac k * a n) := by
      rw [fac_succ]
      -- bottleneck!
      push_cast
      ring
    rw [h2]
    apply isInt_nat_mul
    exact IH




/-
  The partial sums s n, convering to e:

  s n = a 0 + a 1 + ... + a (n-1)   (n terms)

  Defined recursively:
    s 0 = 0
    s (n + 1) = s n + a n
-/

def s (n : ℕ) :=
  match n with
  | 0 => 0
  | n + 1 => s n + a n

lemma s_zero : s 0 = 0 := by rfl

lemma s_succ (n : ℕ) : s (n + 1) = s n + a n := by rfl

lemma s_one : s 1 = 1 := by rw [s_succ, s_zero, a_zero]; numbers

lemma s_two : s 2 = 2 := by rw [s_succ, s_one, a_one]; numbers

lemma s_three : s 3 = 5 / 2 := by rw [s_succ, s_two, a_two]; numbers


lemma s_lt_next (n : ℕ) : s n < s (n + 1) := by
  rw [s_succ]
  addarith [a_pos n]

lemma s_monotone (n : ℕ) (m : ℕ) (hm : m > n) : s n < s m := by
  induction_from_starting_point m, hm with k hk IH
  · exact s_lt_next n
  · calc
    _ < s k := by rel [IH]
    _ < s (k + 1) := by rel [s_lt_next k]

lemma s_monotone' (n : ℕ) (m : ℕ) (hm : m ≥ n) : s n ≤ s m := by
  induction_from_starting_point m, hm with k hk IH
  · rfl
  · calc
    _ ≤ s k := by rel [IH]
    _ ≤ s (k + 1) := by rel [s_lt_next k]

lemma s_nonneg (n : ℕ) : s n ≥ 0 := by
  simple_induction n with n IH
  · rw [s_zero]
  · rw [s_succ]
    addarith [IH, a_pos n]

/-
  Establish that n ! * s (n + 1) is an integer.
  TODO: clean this up! This is probably the most tricky part of this worksheet;
  casting and pushing the casts around is a mess;
  may need specific tooling!
-/



lemma fac_mul_a_integral (n : ℕ) (m : ℕ) (h : n ≤ m) :
    ∃ N : ℕ, (fac m) * (a n)= N := by
  induction_from_starting_point m, h with k hk IH
  · use 1
    rw [fac_mul_a_eq_one]
    push_cast; ring
  · obtain ⟨N, hN⟩ := IH
    use (k + 1) * N
    rw [fac_succ]
    calc
    _ = (k + 1) * ((fac k) * (a n)) := by push_cast; ring
    _ = (k + 1) * N := by rw [hN]
    _ = _ := by push_cast; ring


-- TODO: rewrite using integrality lemmas?
lemma s_integrality (n : ℕ) (m : ℕ) (h : m + 1 ≥ n):
    ∃ N : ℤ, (fac m) * s n = N := by
  simple_induction n with n IH
  · rw [s_zero]
    use 0
    ring
  · have h' : m + 1 ≥ n := by addarith [h]
    obtain ⟨N, hN⟩ := IH h' -- obtain an m from the ∃ in the inductive hypothesis
    obtain ⟨N2, hN2⟩ := fac_mul_a_integral n m (by addarith [h])
    rw [s_succ]
    use N + N2
    push_cast
    rw [←hN, ←hN2]
    ring



/-
  Key inequality for s n
-/

-- alternative: use fac_bound


-- TODO: really need to practice a bit with inverses and inequalities
-- this is a MESS now






lemma a_bound (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    a (n + k) ≤  (c k) * (a n) := by
  simple_induction k with k IH
  · -- base case
    rw [c_zero]
    calc
      a (n + 0) = 1 * a n := by ring
      _ ≤ 1 * a n := by extra
  · -- inductive step
    sorry


lemma s_under_geometric (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    s (n + k) ≤ s n + (a n) * (g k) := by
  simple_induction k with k IH
  · -- base case
    rw [g_zero]
    simp
    extra
  · -- inductive step
    calc
      _ = s (n + k + 1) := by ring
      _ = s (n + k) + a (n + k) := by rw [s_succ]
      _ ≤ s n + (a n) * (g k) + a (n + k) := by rel [IH]
      _ ≤ s n + (a n) * (g k) + (c k) * a n := by rel [a_bound n k hn]
      _ = s n + (a n) * ((g k) + (c k)) := by ring
      _ = s n + (a n) * (g (k + 1)) := by rw [g_succ]


theorem key_bound_s (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    s (n + k) < s n + 2 * (a n)  := by
  have h : a n > 0 := a_pos n
  calc
    _ ≤ s n + (a n) * (g k) := by apply s_under_geometric n k hn
    _ < s n + (a n) * 2 := by rel [geometric_sum_lt_2 k]
    _ = s n + 2 * (a n) := by ring

lemma key_bound_s' (n : ℕ) (m : ℕ) (hm : m ≥ n) (hn : n ≥ 1) :
    s m ≤ s n + 2 * (a n)  := by
  let k := m - n
  have hk : m = n + k := by exact (Nat.sub_eq_iff_eq_add' hm).mp rfl
  calc
    _ = s (n + k)  := by rw [hk]
    _ ≤ s n + 2 * (a n) := by rel [key_bound_s n k hn]
    _ = s n + 2 * (a n) := by ring

lemma s_bounded' (n : ℕ) : s (n + 1) < 3 := by
  have h : 1 ≥ 1 := by numbers
  calc
    _ = s (1 + n) := by ring
    _ < s 1 + 2 * (a 1) := by exact key_bound_s 1 n h
    _ = 3 := by rw [a_one, s_one]; numbers

-- trick: can use `simple_induction` to distinguish
-- between n = 0 and n = k + 1, while ignoring the induction hypothesis ;-)
-- TODO: don't do this!
lemma s_bounded (n : ℕ) : s n < 3 := by
  simple_induction n with k IH
  · rw [s_zero]
    numbers
  · apply s_bounded'

lemma s_abs_bounded (n : ℕ) : |s n| ≤ 3 := by
  rw [abs_of_nonneg]
  · rel [s_bounded n]
  · apply s_nonneg



/-
  The next part shows that the sequence s n is Cauchy, defines e : ℝ to be its
  limit, and establishes a lemma stating that s n converges to e.

  The proofs have been pre-filled, since they require working closely with the
  definitions of ℝ, "Cauchy" and "limit" as implemented in Mathlib. However,
  we only need to use the lemma `s_tends_to_e`, which guarantees that no matter
  how `e : ℝ` was defined, it agrees with the real number e as you know it.

  In partiacul, in the remainder of the worksheet you can ignore the definition
  and only need to use the lemma `s_tends_to_e`.
-/


theorem s_cauchy : IsCauSeq abs s := by
  apply isCauSeq_of_mono_bounded
  · intro n hn
    apply s_abs_bounded n
  · intro n hn
    rel [s_lt_next n]
  · use 0


def e_seq : CauSeq ℝ abs := ⟨fun n ↦ s n, s_cauchy⟩

def e : ℝ := CauSeq.lim e_seq


lemma s_tends_to_e : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - e| < ε := by
  intro ε hε
  have h := CauSeq.equiv_def₃ (CauSeq.equiv_lim e_seq) hε
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  exact hN n hn n (by rfl)



/-
  Deduce some bounds on e
-/


lemma s_lt_e (n : ℕ) : s n < e := by
  by_contra h
  rw [not_lt] at h
  have h2 : e < s (n+1) := by addarith [h, s_lt_next n]
  let ε := s (n+1) - e
  have hε : ε > 0 := by dsimp; addarith [h2]
  obtain ⟨N, hN⟩ := s_tends_to_e ε hε
  let m := max N (n+1)
  have hm : m ≥ N := by exact Nat.le_max_left N (n+1)
  have hm2 : m ≥ n+1 := by exact Nat.le_max_right N (n+1)
  specialize hN m hm
  contrapose hN
  push_neg
  calc
    _ = s (n + 1) - e := by rfl
    _ ≤ s m - e := by addarith [s_monotone' (n + 1) m hm2]
    _ ≤ |s m - e| := by exact le_abs_self (s m - e)

-- if s n ≤ c for all n, then e ≤ c
lemma e_le_of_s_le (c : ℝ) (N : ℕ) (h : ∀ n ≥ N, s n ≤ c) : e ≤ c := by
  by_contra h2
  push_neg at h2
  let ε := e - c
  have hε : ε > 0 := by dsimp; addarith [h2]
  obtain ⟨m, hm⟩ := s_tends_to_e ε hε
  let n := max N m
  have hn : n ≥ N := by exact Nat.le_max_left N m
  have hn2 : n ≥ m := by exact Nat.le_max_right N m
  specialize h n hn
  specialize hm n hn2
  contrapose hm
  push_neg
  calc
    _ = e - c := by rfl
    _ ≤ e - s n := by addarith [h]
    _ ≤ |e - s n| := by exact le_abs_self (e - s n)
    _ = |- (e - s n )| := by rw [abs_neg]
    _ = |s n - e| := by ring

theorem key_bound_e (n : ℕ) (hn : n ≥ 1): e ≤ s n + 2 * (a n) := by
  apply e_le_of_s_le _ 1
  intro m hm
  by_cases h : m ≥ n
  · exact key_bound_s' n m h hn
  · push_neg at h
    have h3 : a n ≥ 0 := by addarith [a_pos n]
    have h2 : 2 * (a n) ≥ 0 := by positivity
    calc
      _ ≤ s n := by rel [s_monotone m n h]
      _ ≤ s n + 2 * (a n) := by extra


theorem e_lt_3 : e < 3 := by
   calc
    e ≤ s 3 + 2 * (a 3) := by exact key_bound_e 3 (by numbers)
    _ = 5 / 2 + 2 * (1 / 6) := by rw [s_three, a_three]
    _ < 3 := by numbers


/-
  We will now prove that e is irrational. Consider the tail

  t n = e - s n = 1 / n! + 1 / (n+1)! + ...

  By the key bound, we have t n ≤ 2 * 1 / n!, so
  n! * t (n + 1) < 1 for n > 1

  Note that n! * s (n + 1) is an integer.

  Now if e is rational, then n! * e is an integer for n big enough

  But then n! * t (n + 1) is an integer/

  This is a contradiction with the fact that n! * t (n + 1) < 1.

  BAH, stuff below is a mess. Write out argument *very carefully*
  on paper first!

-/

def t (n : ℕ) := e - s n

lemma t_def (n : ℕ) : t n = e - s n := by rfl

lemma t_pos (n : ℕ) : 0 < t n := by
  rw [t_def]
  addarith [s_lt_e n]

lemma t_le_twice_a (n : ℕ) (hn : n ≥ 1) : t n ≤ 2 * (a n) := by
  rw [t_def]
  addarith [key_bound_e n hn]


-- KEY INGREDIENT 1:
lemma fac_mul_s_succ_integral (n : ℕ) :
    ∃ N : ℤ, (fac n) * s (n + 1) = N := by
  exact s_integrality (n + 1) n (by rfl)

-- KEY INGREDIENT 2:
lemma fac_mul_t_succ_lt_1 (n : ℕ) (hn : n ≥ 2) :
    (fac n) * (t (n + 1)) < 1 := by
  have h1 : n + 1 ≥ 1 := by addarith [hn]
  have h2 : a n > 0 := by addarith [a_pos n]
  have h3 : a (n + 1) > 0 := by addarith [a_pos (n + 1)]
  have h4 : ((n : ℝ) + 1)⁻¹ ≤ 3⁻¹ := by
    apply inv_le_of_inv_le
    · numbers
    · field_simp; norm_cast; addarith [hn]
  calc
  _ ≤ (fac n) * (2 * a (n + 1)) := by rel [t_le_twice_a (n + 1) h1]
  _ = (fac n) * (2 * (((n : ℝ) + 1)⁻¹ * a n)) := by rw [a_succ]; ring
  _ = ((fac n) * a n) * (2 * ((n : ℝ) + 1)⁻¹) := by ring
  _ = 1 * (2 * ((n : ℝ) + 1)⁻¹) := by rw [fac_mul_a_eq_one n]
  _ = 2 * ((n : ℝ) + 1)⁻¹ := by ring
  _ ≤ 2 * (3)⁻¹ := by rel [h4]
  _ < 1 := by numbers

-- KEY INGREDIENT 3:
-- major bottleneck, make this idiomatic!
lemma fac_mul_t_succ_pos (n : ℕ) : (fac n) * (t (n + 1)) > 0 := by
  apply mul_pos
  · norm_cast; exact fac_pos n
  · exact t_pos (n + 1)


-- source of contradiction
lemma no_int_between_0_and_1 (N : ℤ) (hN : N > 0) (hN2 : N < 1) : False := by
  have h : N ≥ 1 := by exact hN
  have h2 : ¬ N < 1 := by exact Int.not_lt.mpr hN
  contradiction


example (N : ℤ) (h : 0 < (N : ℝ)) : 0 < N := by
  simp_all only [Int.cast_pos]

example (N : ℤ) (h : (N : ℝ) < 1) : N < 1 := by
  norm_cast at *


-- KEY STEP: show that n! * e cannot be an integer!
lemma fac_mul_e_not_integral (n : ℕ) (N : ℤ) (hn : n ≥ 2) :
    (fac n) * e ≠ N := by
  intro hN
  obtain ⟨N2, hN2⟩ := fac_mul_s_succ_integral n
  let N3 := N - N2
  have N3_def : N3 = N - N2 := by rfl
  have h : (fac n) * t (n + 1) = N3 := by
    rw [N3_def, t_def]
    push_cast
    rw  [←hN, ←hN2]
    ring
  have h2 : (N3 : ℝ) > 0 := by
    rw [←h]
    exact fac_mul_t_succ_pos n
  norm_cast at h2
  have h3 : (N3 : ℝ) < 1 := by
    rw [←h]
    exact fac_mul_t_succ_lt_1 n hn
  norm_cast at h3
  exact no_int_between_0_and_1 N3 h2 h3

#print axioms fac_mul_e_not_integral


-- TODO: make this idiomatic!
lemma fac_div_integral (q : ℕ) (hq : q > 0) : (fac q) = q * fac (q - 1) := by
  have h : (q - 1) + 1 = q := by exact Nat.sub_add_cancel hq
  rw [← h]
  rw [fac_succ]
  rw [h]



lemma e_rational_factorial :
    (∃ p q : ℕ, q > 0 ∧ e = p / q) → (∃ n > 1, ∃ N : ℕ, (fac n) * e = N) := by
  intro h
  obtain ⟨p, q, hq, he⟩ := h
  use q + 1
  constructor
  · addarith [hq]
  · rw [he]
    rw [fac_succ]
    use fac (q - 1) * p * (q + 1)
    rw [fac_div_integral]
    push_cast
    field_simp
    ring
    exact hq




  theorem e_irrational : ¬ ∃ p q : ℕ, q > 0 ∧ e = p / q := by
  intro h
  obtain ⟨n, hn, N, hN⟩ := e_rational_factorial h
  have h : (n - 1) + 1 = n := by exact Nat.sub_add_cancel (by addarith [hn])
  have h2: ∃ N2 : ℤ, (fac n) * s (n - 1) = N2 := by exact s_integrality (n - 1) n (by addarith [h])
  obtain ⟨N2, hN2⟩ := h2
  have h3 : ∃ N3 : ℤ, (fac n) * t (n - 1) = N3 := by
    rw [t_def]
    use N - N2
    push_cast
    rw [←hN, ←hN2]
    ring
  obtain ⟨N3, hN3⟩ := h3
  have h4 : (N3 : ℝ) < 1 := by
    rw [← hN3]
    -- apply fac_mul_t_succ_lt_1
    sorry
  sorry

#print axioms e_irrational
