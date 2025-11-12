import Library.Basic
noncomputable section

/- # Recap and consolidation -/

/-
  ## Geometric series

  The function below defines for all `c : ℝ` and `n : ℕ` the sum
    `geom c n = 1 + c + c ^ 2 + ... + c ^ (n-1)` (so there are `n` terms)
  It can be manipulated using the two defining lemmas:
    - `geom_zero c : geom c 0 = 0` (empty sum)
    - `geom_succ c n : geom c (n + 1) = (geom c n) + c ^ n`
-/

def geom (c : ℝ) (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => (geom c n) + c ^ n

lemma geom_zero (c : ℝ) : geom c 0 = 0 := by rfl

lemma geom_succ (c : ℝ) (n : ℕ) :
    geom c (n + 1) = (geom c n) + c ^ n := by rfl

/-
  Sanity checks: let's make sure this matches our expectations!
-/

lemma geom_one (c : ℝ) : geom c 1 = 1 := by
  rewrite [geom_succ, geom_zero]; algebra

lemma geom_two (c : ℝ) : geom c 2 = 1 + c := by
  rewrite [geom_succ, geom_one]; algebra

lemma geom_three (c : ℝ) : geom c 3 = 1 + c + c ^ 2 := by
  rewrite [geom_succ, geom_two]; algebra

lemma geom_base_one (n : ℕ) : geom 1 n = n := by
  simple_induction n with k IH
  · rewrite [geom_zero]; algebra
  · rewrite [geom_succ]
    calc
      geom 1 (k + 1) = geom 1 k + 1 := by rewrite [geom_succ]; algebra
      _ = k + 1 := by rewrite [IH]; algebra

/-
  The main result, version 1, which holds for all `c : ℝ`:
-/

lemma geom_series (c : ℝ) (n : ℕ) : (1 - c) * geom c n = 1  - c ^ n := by
  simple_induction n with k IH
  · rewrite [geom_zero]; algebra
  · rewrite [geom_succ]
    calc
      (1 - c) * ((geom c k) + c ^ k) = (1 - c) * c ^ k + (1 - c) * geom c k := by algebra
      _ = 1 - c ^ (k + 1) := by rewrite [IH]; algebra

/-
  Version 2, probably more familiar, but requires the assumption that `1 - c ≠ 0`:
-/

lemma geom_series' (c : ℝ) (n : ℕ) (h : 1 - c ≠ 0) : geom c n = (1 - c ^ n) / (1 - c) := by
  simple_induction n with k IH
  · rewrite [geom_zero]; algebra
  · rewrite [geom_succ, IH]; algebra


/-
  ## The harmonic series

  We define the harmonic series
    `s n = 1 + 1/2 + 1/3 + ... + 1/n`
  Note that there are `n` terms in the sum. The first few values are:
    `s 0 = 0` (empty sum)
    `s 1 = 1`
    `s 2 = 1 + 1/2 = 3/2`
    `s 3 = 1 + 1/2 + 1/3 = 11/6`
  We will prove that this series diverges, that is that `s n` is unbounded as
  `n` goes to infinity.
-/


/-
  First the definition!
-/
def s (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => s n + 1 / (n + 1)

/-
  This defines for every `n : ℕ` a real number `s n : ℝ`. To manipulate it, you
  use the following two lemmas:
   - `s_zero : s 0 = 0`
   - `s_succ n : s (n + 1) = s n + 1 / (n + 1)`
  Together they completely determine `s n` for all `n : ℕ`.
-/

lemma s_zero : s 0 = 0 := by rfl

lemma s_succ (n : ℕ) : s (n + 1) = s n + 1 / (n + 1) := by rfl

/-
  Now let's do some sanity checks to make sure `s n` matches our expectations.
-/

lemma s_one : s 1 = 1 := by rewrite [s_succ, s_zero]; numbers

lemma s_two : s 2 = 3 / 2 := by rewrite [s_succ, s_one]; numbers

lemma s_three : s 3 = 11 / 6 := by rewrite [s_succ, s_two]; numbers


/-
  To practice a bit more, let's prove a simple identity for `s (n + 2)`.
  While proving this, you will often see `↑n` in the right hand window. This is
  Lean's way of telling you that it is considering `n` as a real number.
-/

example (n : ℕ) : s (n + 2) = s n + 1 / (n + 1) + 1 / (n + 2) := by
  rewrite [s_succ, s_succ]
  algebra



/-
  Let us now prove some simple properties of the harmonic series `s n`.
-/

lemma s_monotone (n : ℕ) : s n ≤ s (n + 1) := by
  rewrite [s_succ]
  extra

/-
  Now use this lemma to prove that `s n ≥ 0` for all `n : ℕ`. This can be done
  using `simple_induction`, and `apply` to use the lemma `s_monotone`.
-/
lemma s_pos (n : ℕ) : s n ≥ 0 := by
  simple_induction n with k IH
  · rewrite [s_zero]; numbers
  · calc
      s (k + 1) ≥ s k := by apply s_monotone k
      _ ≥ 0 := by apply IH


/-
  We will prove that for every natural number `N` there is a `n` such that `s m ≥ N`
  for all `m ≥ n`. So eventually, the series will be larger than any given
  natural number.

  As a warming up, let's prove that `s m ≥ 2` for all `m ≥ 4`. This can be done
  using `induction_from_starting_point`.
-/

example (m : ℕ) (h : m ≥ 4) : s m ≥ 2 := by
  induction_from_starting_point m, h with k hk IH
  · rewrite [s_succ, s_three]; numbers
  · rewrite [s_succ]
    calc
      s (k + 1) ≥ s k := by apply s_monotone k
      _ ≥ 2 := by apply IH


/-
  If you want to play around a bit, state and prove that:
    `s m ≥ 3` for all `m ≥ 11`
  The harmonic series grows very slowly, so this quickly goes out of hand. For example:
    `s m ≥ 10` for all `m ≥ 12367`
  I don't recommend you try to prove this now.
-/




/-
  We now move towards proving the divergence of the harmonic series. The key
  step is theorem
    `s_double_bound n h : s (2 * n) ≥ s n + 1/2`
  for `n : ℕ` and `h : n > 0`.

  To prove this, we will need some lemmas first.
-/


lemma inverse_le (a b : ℝ) (h : a ≤ b) (ha : a > 0) : 1 / a ≥ 1 / b := by
  exact one_div_le_one_div_of_le ha h

/-
  There is a subtlety in the next lemma: `n` is a natural number, but we need to
  divide `1` by `2 * n + 2` and `2 * n + 1` as *real numbers*. The
  funny-looking `(1 : ℝ)` in the statement is to tell Lean to consider `1` as a
  real number. Lean then automatically converts the other players in the
  inequality to real numbers.
-/
lemma fractions_estimate (n : ℕ) (h : n > 0) : (1 : ℝ) / (2 * n + 2) ≤ 1 / (2 * n + 1) := by
  -- let's first establish that `2 * n + 1 ≤ 2 * n + 2` in the real numbers
  have h2 : (2 * n + 1 : ℝ) ≤ (2 * n + 2 : ℝ) := by linarith
  -- Finish the proof. It may be useful to establish that `2 * n + 1 > 0` in the real numbers first.
  have h3 : (2 * n + 1 : ℝ) > 0 := by positivity
  apply inverse_le (2 * n + 1) (2 * n + 2) h2 h3


lemma s_twice_succ (n : ℕ) (h : n > 0) : s (2 * (n + 1)) ≥ s (2 * n) + 1 / (n + 1) := by
  calc
    s (2 * (n + 1)) = s ((2 * n + 1) + 1) := by algebra
    _ = s (2 * n + 1) + 1 / (2 * n + 2) := by rewrite [s_succ]; algebra
    _ = s (2 * n) + 1 / (2 * n + 1) + 1 / (2 * n + 2) := by rewrite [s_succ]; algebra
    _ ≥ s (2 * n) + 1 / (2 * n + 2) + 1 / (2 * n + 2) := by rel [fractions_estimate n h]
    _ = s (2 * n) + 1 / (n + 1)  := by algebra

lemma s_double_bound (n : ℕ) (h : n > 0) : s (2 * n) ≥ s n + 1/2 := by
  induction_from_starting_point n, h with k hk IH
  · rewrite [s_two, s_one]; numbers
  · rewrite [s_succ]
    calc
      s (2 * (k + 1)) ≥ s (2 * k) + 1 / (k + 1) := by apply s_twice_succ k hk
      _ ≥  (s k + 1 / 2) + 1 / (k + 1) := by rel [IH]
      _ = (s k + 1 / (k + 1)) + 1 / 2 := by algebra

lemma harmonic_pow_two (n : ℕ) : s (2 ^ n) ≥ n / 2 := by
  simple_induction n with k IH
  · simp;
    rewrite [s_one]; numbers
  · calc
      s (2 ^ (k + 1)) = s (2 * 2 ^ k) := by algebra
      _ ≥ s (2 ^ k) + 1 / 2 := by apply s_double_bound (2 ^ k) (by positivity)
      _ ≥ k / 2 + 1 / 2 := by rel [IH]
      _ = (k + 1) / 2 := by algebra



/-
   Now let's prove divergence: for every `n : ℕ` there is an `N` such that `s m ≥ n` for all
   `m ≥ N`. Use the lemma `harmonic_pow_two` to prove this.

   Follow the following steps:

   1) figure out which value `N = C` to use (as a function of `n`) and start with `use C`
   2) use `intro h` to introduce the hypothesis `m ≥ C`
   3) now use `induction_from_starting_point` to prove that the ineqality holds
      for all `m ≥ C`
-/


theorem harmonic_diverges (N n : ℕ) : ∃ n : ℕ, m ≥ n → s m ≥ N := by
  use 2 ^ (2 * N)
  intro h
  induction_from_starting_point m, h with k hk IH
  · calc
       s (2 ^ (2 * N)) ≥ (2 * N : ℕ) / 2 := by apply harmonic_pow_two (2 * N)
      _ = N := by algebra
  · rewrite [s_succ]
    calc
      s (k + 1) ≥ s k := by apply s_monotone k
      _ ≥ N := by apply IH
