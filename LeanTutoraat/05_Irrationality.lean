import Library.Basic
noncomputable section


/-
  # Final group project: proving that `e` is irrational

  In this worksheet, we will prove that `e` is irrational. This is intended as a
  larger group project, where participants can work on different parts of the proof
  in parallel.

  Below is a detailed skeleton proof, with the argument already split into many
  smaller lemmas. You will work on those in parallel, replacing all the
  `sorry`s with actual proofs, until the proof of the main theorem
  no longer uses any `sorry`.
-/



/-
  ## Part I: Bounds on the factorial function

  The factorial function `fac`, with values in `ℕ`. You should manipulate
  this function by using the following two lemmas:
  - `fac_zero : fac 0 = 1`
  - `fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n`
-/

def fac (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * fac n

lemma fac_zero : fac 0 = 1 := by rfl

lemma fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by rfl


/-
  Now let's prove some basic facts about the factorial function.
-/

lemma fac_one : fac 1 = 1 := by
  sorry

lemma fac_two : fac 2 = 2 := by
  sorry

lemma fac_three : fac 3 = 6 := by
  sorry

-- use `simple_induction` to prove this
lemma fac_pos (n : ℕ) : fac n > 0 := by
  sorry

/-
  Hint: `linarith` or `positivity` can prove this, but by default they cannot "see"
  the fact `fac n > 0` (proved above). You'll need to make it visible
  with a `have` statement first.
-/
lemma fac_ne_zero (n : ℕ) : fac n ≠ 0 := by
  sorry

lemma fac_ge_one (n : ℕ) : fac n ≥ 1 := by
  sorry

lemma fac_strictly_monotone (n : ℕ) (h : n ≥ 1) : fac (n + 1) > fac n := by
  sorry

-- to prove something holds for all `n ≥ 2` you can use `induction_from_starting_point`
lemma fac_gt_one (n : ℕ) (h : n ≥ 2) : fac n > 1 := by
  sorry

lemma fac_gt_of_gt (n m : ℕ) (h1 : n ≥ m + 1) (h2 : m ≥ 1): fac n > fac m := by
  induction_from_starting_point n, h1 with k hk IH
  · sorry
  · sorry

lemma fac_ge_of_ge (n m : ℕ) (h : m ≥ n) : fac m ≥ fac n := by
  sorry

lemma fac_ge_two (n : ℕ) (hn : n ≥ 2) : fac n ≥ 2 := by
  sorry

lemma fac_prev (n : ℕ) (h1 : n ≥ 1) : fac n = fac (n - 1) * n := by
  sorry




/-
  This is the `big boss` of Part I. It is the key inequality on which the proof of
  the irrationality of `e` is based.

  I recommend you write out the proof in detail on paper first, especially for the
  inductive step.
-/
theorem fac_bound (n : ℕ) (k : ℕ) (hn : n > 0) :
    fac (n + k) ≥ 2 ^ k * fac n := by
  simple_induction k with k IH
  · -- base case
    sorry
  · -- inductive step
    sorry

/-
  We will apply `fac_bound` above to say something about `1 / fac (n + k)`. For this, it will
  be useful to know that `2 ^ k * fac n` is positive.

  Hint: `positivity` can do this, but think a bit about what it needs to know to conclude.
  Remember: tactics like `positivity` or `linarith` cannot see what we have proven above
  without reminding them.
-/
lemma pow_two_mul_fac_pos (n : ℕ) (k : ℕ) : 0 < 2 ^ k * fac n := by
  sorry


/-
  ## Part II: the term `a n := 1 / n!`
-/

/-
  We will define `e` as `∑_n 1 / n!`. In this part, we consider the term `a n := 1 / n!`.
  There is a subtlety here: we have defined `fac n` as a natural number, and we want to consider
  its inverse as a real number. To avoid lots of technicalities later on,
  we separate out the transition from "natural number `n!`" to "real number `1 / n!`",
  and prove the elementary properties of this function.
-/

def nat_inv (n : ℕ) : ℝ := (n : ℝ)⁻¹

lemma nat_inv_def (n : ℕ) : nat_inv n = (n : ℝ)⁻¹ := by rfl

/-
  Whenever you see an expression `nat_inv n`, you can use `rewrite [nat_inv_def]` to
  replace it with `(↑n)⁻¹`. Lean will use the arrow `↑` is there to remind you that it
  is treating the (a priori) natural number `n` as a real number now.
-/
lemma nat_inv_one : nat_inv 1 = 1 := by
  sorry

lemma nat_inv_two : nat_inv 2 = 1 / 2 := by
  sorry

lemma nat_inv_pos (n : ℕ) (hn : n > 0) : nat_inv n > 0 := by
  sorry

/-
  Hint: `linarith` or `positivity` can prove this, but by defaultthey cannot "see"
  the fact `nat_inv n > 0` proved above. You'll need to make it visible
  with a `have` statement first.
-/
lemma nat_inv_ne_zero (n : ℕ) (hn : n > 0) : nat_inv n ≠ 0 := by
  sorry

lemma nat_inv_mul (n m : ℕ) : nat_inv (n * m) = nat_inv n * nat_inv m := by
  sorry

/-
  In the lemma below, it may be useful to use the following lemma:
    `inv_le_inv_of_le (h1 : 0 < a) (h2 : a ≤ b) : b⁻¹ ≤ a⁻¹`
-/
lemma nat_inv_le (n m : ℕ) (h : n ≥ m) (hm : m > 0) : nat_inv n ≤ nat_inv m := by
  sorry
/-
  In the lemma below, it may be useful to use the following lemma:
    `inv_lt_inv_of_lt (h1 : 0 < a) (h2 : a < b) : b⁻¹ < a⁻¹`
-/
lemma nat_inv_lt (n m : ℕ) (h : n > m) (hm : m > 0) : nat_inv n < nat_inv m := by
  sorry

lemma nat_inv_le_one (n : ℕ) (hn : n > 0) : nat_inv n ≤ 1 := by
  sorry

lemma nat_inv_lt_one (n : ℕ) (hn : n > 1) : nat_inv n < 1 := by
  sorry


/-
  Now define `a n := nat_inf fac n`, so `a n = 1 / n!`. The first few values are:
  - `a 0 = 1 / 0! = 1`
  - `a 1 = 1 / 1! = 1`
  - `a 2 = 1 / 2! = 1 / 2`
  - `a 3 = 1 / 3! = 1 / 6`
-/

def a (n : ℕ) : ℝ := nat_inv (fac n)

lemma a_def (n : ℕ) : a n = nat_inv (fac n) := by rfl


/-
  A few sanity checks to make sure `a n` behaves as expected.
-/
lemma a_zero : a 0 = 1 := by
  sorry

lemma a_one : a 1 = 1 := by
  sorry

lemma a_two : a 2 = 1 / 2 := by
  sorry

lemma a_three : a 3 = 1 / 6 := by
  sorry

lemma a_succ (n : ℕ) : a (n + 1) = a n / (n + 1) := by
  sorry


/-
  Most of the lemmas below follow from applying corresponding properties of `nat_inv` and
  `fac`. Have a look at the lemmas above, and use `apply` to apply them.
-/

-- example:
lemma a_pos (n : ℕ) : a n > 0 := by
  rewrite [a_def]
  apply nat_inv_pos
  apply fac_pos

lemma a_le_one (n : ℕ) : a n ≤ 1 := by
  sorry

lemma a_le (n m : ℕ) (h : n ≥ m) : a n ≤ a m := by
  sorry

lemma a_lt (n m : ℕ) (h : n > m) (hn : m > 0) : a n < a m := by
  sorry

lemma fac_mul_a_eq_one (n : ℕ) : fac n * a n = 1 := by
  sorry


/-
  We can now use `fac_bound` from above to prove the following key inequality
  for `a n`, namely
    `a (n + k) ≤ (1/2) ^ k * (a n)`
  You'll need to use `fac_bound` and `pow_two_mul_fac_pos` to prove this.
-/
theorem a_bound (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    a (n + k) ≤  (1/2) ^ k * (a n) := by
  -- it is useful to first prove the following:
  have h : (1/2) ^ k * (a n) = nat_inv (2 ^ k * fac n) := by
    sorry
  -- now use `h` and `a_def` to rewrite the goal into an inequality of `nat_inv`'s
  -- and finish the proof.
  sorry



/-
  # Part III: bounding the geometric series Σ_{i=0}^{k-1} 2^{-i}

  Let `g n := 1 + 1/2 + 1/4 + ... + 1/2^(n-1)`, so there are `n` terms in the sum.
  The first few values are:
  - `g 0 = 0` (empty sum)
  - `g 1 = 1`
  - `g 2 = 1 + 1/2 = 3/2`
  - `g 3 = 1 + 1/2 + 1/4 = 7/4`
  In this part, we prove that `g n < 2` for all `n`.
-/

def g (n : ℕ) : ℝ := match n with
  | 0 => 0
  | n + 1 => g n + (1/2) ^ n

/-
  As usualy, you can ignore the *definition* of `g` and just use the two defining lemmas
  - `g_zero : g 0 = 0`
  - `g_succ : g (n + 1) = g n + (1/2) ^ n`
-/

lemma g_zero : g 0 = 0 := by rfl

lemma g_succ (n : ℕ) : g (n + 1) = g n + (1/2) ^ n := by rfl

/-
  Now let's do some sanity checks to make sure `g n` matches our expectations.
-/

lemma g_one : g 1 = 1 := by
  sorry

lemma g_two : g 2 = 3 / 2 := by
  sorry

lemma g_three : g 3 = 7 / 4 := by
  sorry



/-
  Prove a closed formula for `g n`, by induction on `n`.
-/
lemma g_formula (n : ℕ) : g n = 2 - 2 * (1/2) ^ n := by
  sorry

/-
  Use this to prove the following basic inequality:
-/
theorem g_lt_2 (n : ℕ) : g n < 2 := by
  sorry



/-
  ## Part IV: the partial sums `s n`

  Recall that `a n = 1 / n!`. We will define the number `e` through the series `e = ∑_n a n`.
  To prepare for this, we consider the partial sums:
    `s n = a 0 + a 1 + ... + a (n-1)`   (n terms)
  They are defined recursively by:
    `s 0 = 0`
    `s (n + 1) = s n + a n`
  The first few values of `s n` are:
  - `s 0 = 0` (empty sum)
  - `s 1 = a 0 = 1`
  - `s 2 = a 0 + a 1 = 1 + 1 = 2`
  - `s 3 = a 0 + a 1 + a 2 = 1 + 1 + 1/2 = 5/2`
-/

def s (n : ℕ) :=
  match n with
  | 0 => 0
  | n + 1 => s n + a n

/-
  As usual, you can ignore the *definition* of `s` and just use the two defining lemmas
  - `s_zero : s 0 = 0`
  - `s_succ : s (n + 1) = s n + a n`
-/

lemma s_zero : s 0 = 0 := by rfl

lemma s_succ (n : ℕ) : s (n + 1) = s n + a n := by rfl

/-
  Now let's do some sanity checks to make sure `s n` matches our expectations.
-/

lemma s_one : s 1 = 1 := by
  sorry

lemma s_two : s 2 = 2 := by
  sorry

lemma s_three : s 3 = 5 / 2 := by
  sorry


/-
  Using `s_succ`, this reduces to `s n + a n > s n`. The tactics `extra` or `linarith`
  can prove this, but they need to *see* the fact that `a n > 0`. Remind them by
  including a `have` statement (which you can prove by applying the lemma `a_pos`
  above).
-/
lemma s_strictly_monotone (n : ℕ) : s n < s (n + 1) := by
  sorry

-- to prove something holds for all `m > n`, you can use `induction_from_starting_point`
lemma s_lt_of_lt (n : ℕ) (m : ℕ) (h : n < m) : s n < s m := by
  induction_from_starting_point m, h with k hk IH
  · sorry
  · sorry

-- variation:
lemma s_le_of_le (n : ℕ) (m : ℕ) (h : n ≤ m) : s n ≤ s m := by
  sorry

lemma s_nonneg (n : ℕ) : s n ≥ 0 := by
  sorry


/-
  This is the *big boss* theorem of Part IV.

  The result is based on `a_bound` from Part II. Look up the statement of `a_bound` first.

  I strongly suggest you use pen and paper to write out a detailed proof of the inductive step
  first.
-/
theorem s_geometric_bound (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    s (n + k) ≤ s n + (a n) * (g k) := by
  simple_induction k with k IH
  · sorry
  · sorry

/-
  Using `g_lt_2` this implies that `s (n + k) < s n + 2 * (a n)`.
-/
lemma s_bound (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    s (n + k) < s n + 2 * (a n)  := by
  -- remind Lean that `a n > 0`, so that `linarith`, `rel`, ... can use this
  have h : a n > 0 := a_pos n
  -- now finish the proof using `s_geometric_bound` and `g_lt_2`
  sorry


/-
  Variant: we eliminate `k` by replacing `n + k` with any `m` such that `m ≥ n`:
-/
lemma s_bound_variant (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ n) : s m < s n + 2 * (a n) := by
  -- first, let's define `k` as `m - n`
  let k := m - n
  -- `hk` is the hypothesis that `m = n + k`
  have hk : m = n + k := by exact (Nat.sub_eq_iff_eq_add' hm).mp rfl
  -- now finish the proof
  sorry


/-
  Since `s` is increasing, the condition that `m ≥ n` is unnecessary!
-/

theorem s_key_bound (n m : ℕ) (hn : n ≥ 1) : s m < s n + 2 * (a n) := by
  by_cases hm : m ≥ n
  · -- either `m ≥ n`, then this is `s_bound_variant` above
    sorry
  · -- or `¬ m ≥ n`, then we have `m < n`:
    push_neg at hm
    -- now finish the proof
    sorry



/-
  Application: we can use `key_bound_s` to prove that `s n` is less than `3`
  for all `n`. Indeed, taking `m = 2` we find `s n < s 2 + 2 * (a 2) = 3`.
-/
lemma s_lt_three (n : ℕ) : s n < 3 :=
  sorry


/-
  ## Part V: Integrality and Rationality

  We will prove that `e` is irrational by proving that `(fac N) * e` is not an integer for any
  positive natural number `N`.

  For `x : ℝ`, we write `isInt x` for the hypothesis that `x` is an integer. You
  can use the following lemmas to reason about integrality:
    - `isInt_zero : isInt 0`
    - `isInt_one : isInt 1`
    - `isInt_nat (n : ℕ) : isInt (n : ℝ)`
    - `isInt_int (n : ℤ) : isInt (n : ℝ)`
    - `isInt_add (hx : isInt x) (hy : isInt y) : isInt (x + y)`
    - `isInt_sub (hx : isInt x) (hy : isInt y) : isInt (x - y)`
    - `isInt_mul (hx : isInt x) (hy : isInt y) : isInt (x * y)`
    - `isInt_nat_mul (hx : isInt x) (n : ℕ) : isInt (↑n * x)`

  Similarly, `isRat x` is the hypothesis that `x` is a rational number. You
  can use the following lemmas:
    - `isRat_zero : isRat 0`
    - `isRat_one : isRat 1`
    - `isRat_nat (n : ℕ) : isRat (n : ℝ)`
    - `isRat_int (n : ℤ) : isRat (n : ℝ)`
    - `isRat_inv_nat (n : ℕ) (h : n > 0) : isRat (n : ℝ)⁻¹`
    - `isRat_add (hx : isRat x) (hy : isRat y) : isRat (x + y)`
    - `isRat_mul (hx : isRat x) (hy : isRat y) : isRat (x * y)`
    - `isRat_sub (hx : isRat x) (hy : isRat y) : isRat (x - y)`
-/

/-
  Let's do a few warming up exercises to get used to these. They won't be
  strictly necessary in the rest of the worksheet, but should help you get
  familiar with `isInt` and `isRat` before diving into the important bits.
-/
example : isInt 2 := by
  sorry

-- hint: first establish `h : 2 > 0` and then use `apply isRat_inv_nat` with the correct arguments
example : isRat 2⁻¹ := by
  sorry

example : isRat (5/8) := by
  -- without the (_ : ℝ), lean will not know to treat 5 and 8 as real numbers
  have h : (5 : ℝ) / 8  = 5 * (8⁻¹) := by numbers
  -- now finish the proof using the lemmas above.
  sorry

-- another exercise to get used to the lemmas above: the square of an integer is an integer
example (x : ℝ) (h : isInt x) : isInt (x ^ 2) := by
  sorry

/-
  Key integrality lemma about `a_n`:
    `(fac m) * a n` is an integer for all `m ≥ n`.
  Hint: look up `fac_mul_a_eq_one` and `fac_succ` above.
-/
lemma isInt_fac_mul_a (n m : ℕ) (h : n ≤ m) : isInt (fac m * a n) := by
  induction_from_starting_point m, h with k hk IH
  · sorry
  · -- in the following identity we force Lean to treat `k + 1` as a natural number
    have h2 : fac (k + 1) * a n = (k + 1 : ℕ) * (fac k * a n) := by
      -- first prove the identity `h2`
      sorry
    -- now finish the proof of the induction step.
    sorry


/-
  Key integrality lemma about `s n`:
    `(fac m) * s n` as soon as `m + 1 ≥ n`.
  I recommend you write out the induction step on paper first!
-/
theorem isInt_fac_mul_s (n : ℕ) (m : ℕ) (h : m + 1 ≥ n):
    isInt ((fac m) * s n) := by
  simple_induction n with k IH
  · sorry
  · -- let's first relate `(fac m) * s (k + 1)` and `(fac m) * s k`
    have h2 : (fac m) * s (k + 1) = (fac m) * s k + (fac m) * a k := by
      sorry
    -- now finish the proof of the induction step.
    sorry


/-
  The following lemma says that if `x` is rational, then there exists an `n ≥ 1` such that
  `(fac n) * x` is an integer. (Convince yourself of this fact!). This will be used to prove (by
  contradiction) that `e` is irrational: we'll show that `(fac n) * e` can never be integral.

  Hint: use `rewrite [fac_prev n h1]` to express `fac n` as a
  product of `fac (n - 1)` and `n`.
-/

lemma fac_mul_isInt_of_isRat (x : ℝ) (h : isRat x) :
    ∃ n : ℕ, n ≥ 1 ∧ isInt ((fac n) * x) := by
  -- by definition of IsRat, there exists an `n > 0` such that `n * x` is an integer.
  obtain ⟨n, h1, h2⟩ := h
  use n
  -- we need to show that `n ≥ 1` and that `(fac n) * x` is an integer.
  constructor
  · -- prove that `n ≥ 1`
    sorry
  · -- prove that `(fac n) * x` is an integer
    sorry



/-
  Variation: we'll actually need a slightly stronger conclusion: that we can take `n ≥ 2`.
  This clearly follows from the previous lemma: if we had `n = 1`, so that `(fac 1) * x` is
  integral, then `x` is integeral and hence also `(fac 2) * x` is integral so we could have
  taken `n = 2` instead of `n = 1`.
-/

theorem rationality_criterion (x : ℝ) (h : isRat x) :
    ∃ n : ℕ, n ≥ 2 ∧ isInt ((fac n) * x) := by
  -- by the previous lemma, there is an `n ≥ 1` such that `(fac n) * x` is integral.
  obtain ⟨n, h1, h2⟩ := fac_mul_isInt_of_isRat x h
  -- case distinction on `n`:
  by_cases h3 : n ≥ 2
  · -- either `n ≥ 2` and then we can use the previous lemma directly
    use n
    exact ⟨h3, h2⟩
  · -- or not `n ≥ 2`. The following tactic rewrites this to `n < 2`.
    push_neg at h3
    -- now we can just use `n = 2`.
    use 2
    -- we need to prove that `2 ≥ 2` and that `(fac 2) * x` is an integer.
    constructor
    · -- prove that `2 ≥ 2`
      sorry
    · -- prove that `(fac 2) * x` is an integer
      sorry


/-
  ## Part VI: The number `e` as limit of the sequence `s n`

  So far, we have not mentioned the number `e` yet! In this part, we define `e` as follows:
  - we show that the sequence `s n` is Cauchy, and hence has a limit
  - we define `e` to be this limit.
  The details are a bit technical, since they require working closely with the
  how `ℝ`, "Cauchy" and "limit" have been implemented in Lean. For this reason,
  this section is already pre-filled with proofs.

  To be able to *use* the number `e`, we include proofs of two lemmas:
  - `s_lt_e`, which states that `s n < e` for all `n`
  - `e_le_of_s_le`, which states that if `s n ≤ c` for all `n`, then `e ≤ c`.

  In the remainder of the worksheet, you will only need to know these two facts about `e`.
  Convice yourself that these  completely determine the number `e`! In particular,
  you can trust that the number `e` defined below agrees with the real number `e` as you know it.
-/

/-
  `|s n| ≤ 3`, so `s n` is a bounded sequence. Uses the inequalities `0 ≤ s n` and `s n < 3`
  proven above.
-/
lemma s_abs_bounded (n : ℕ) : |s n| ≤ 3 := by
  rw [abs_of_nonneg]
  · rel [s_lt_three n]
  · apply s_nonneg

/-
  `s n` is bounded and monotone, so it is a Cauchy sequence.
-/
lemma s_cauchy : IsCauSeq abs s := by
  apply isCauSeq_of_mono_bounded
  · intro n hn
    apply s_abs_bounded n
  · intro n hn
    rel [s_strictly_monotone n]
  · use 0

/-
  Cauchy sequences have a limit, we denote the limit of `s n` by `e`.
-/
def e_seq : CauSeq ℝ abs := ⟨fun n ↦ s n, s_cauchy⟩

def e : ℝ := CauSeq.lim e_seq

/-
  This lemma spells out what it means for `s n` to converge to `e`.
-/
lemma s_tends_to_e : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - e| < ε := by
  intro ε hε
  have h := CauSeq.equiv_def₃ (CauSeq.equiv_lim e_seq) hε
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  exact hN n hn n (by rfl)

/-
  Since `s n` is increasing and converges to `e`, we have
  `s n < e` for all `n`.
-/
lemma s_lt_e (n : ℕ) : s n < e := by
  by_contra h
  rw [not_lt] at h
  have h2 : e < s (n+1) := by linarith [h, s_strictly_monotone n]
  let ε := s (n+1) - e
  have hε : ε > 0 := by dsimp; linarith [h2]
  obtain ⟨N, hN⟩ := s_tends_to_e ε hε
  let m := max N (n+1)
  have hm : m ≥ N := by exact Nat.le_max_left N (n+1)
  have hm2 : m ≥ n+1 := by exact Nat.le_max_right N (n+1)
  specialize hN m hm
  contrapose hN
  push_neg
  calc
    _ = s (n + 1) - e := by rfl
    _ ≤ s m - e := by linarith [s_le_of_le (n + 1) m hm2]
    _ ≤ |s m - e| := by exact le_abs_self (s m - e)


/-
  If `s n < c` for all `n`, then `e ≤ c`.
-/
lemma e_le_of_s_le (c : ℝ) (h : ∀ n, s n < c) : e ≤ c := by
  by_contra h2
  push_neg at h2
  let ε := e - c
  have hε : ε > 0 := by dsimp; addarith [h2]
  obtain ⟨N, hN⟩ := s_tends_to_e ε hε
  let n := N
  specialize h N
  specialize hN N
  contrapose hN
  push_neg
  constructor
  · rfl
  · calc
    _ = e - c := by rfl
    _ ≤ e - s N := by addarith [h]
    _ ≤ |e - s N| := by exact le_abs_self (e - s n)
    _ = |- (e - s N )| := by rw [abs_neg]
    _ = |s N - e| := by ring




/-
  ## Part VII: The tail `t n` of the series

  We will now prove that e is irrational. A key player is the "tail"
    `t n = e - s n = 1 / n! + 1 / (n+1)! + ...`
  of the series defining `e`.

  We will establish that for all `n ≥ 2` we have:
   `0 < (fac n) * t (n + 1) < 1`

  Later, we will show that if `e` were rational, then `(fac n) * t (n + 1)` would be
  integral for some `n` large enough. But this is absurd, since no number strictly between
  0 and 1 can be an integer.
-/

/-
  First we establish a key inequality on `e`.
-/

theorem key_bound_e (n : ℕ) (hn : n ≥ 1): e ≤ s n + 2 * (a n) := by
  -- by `e_le_of_s_le` it suffices to show that `s m < s n + 2 * (a n)` for all `m`.
  apply e_le_of_s_le
  intro m
  -- finish the proof by applying `s_key_bound` with the correct arguments.
  apply s_key_bound n m hn


/-
  Now consider the tail `t n`.
-/

def t (n : ℕ) := e - s n

lemma t_def (n : ℕ) : t n = e - s n := by rfl

/-
  Let's do a quick sanity check to make sure `t n` behaves as expected.
-/

lemma t_zero : t 0 = e := by
  rewrite [t_def]
  rewrite [s_zero]
  algebra

lemma t_add_s (n : ℕ) : t n + s n = e := by
  rewrite [t_def]
  algebra

/-
  Now let us prove lower and upper bounds for `t n`.
-/
lemma t_pos (n : ℕ) : 0 < t n := by
  -- hint: use `s_lt_e`, introduced above.
  rewrite [t_def]
  linarith [s_lt_e n]

lemma t_le_twice_a (n : ℕ) (hn : n ≥ 1) : t n ≤ 2 * (a n) := by
  -- let's first spell out the definition of `t n`
  rewrite [t_def]
  have h : e ≤ s n + 2 * (a n) := by apply key_bound_e n hn
  linarith

/-
  We use these to prove lower and upper bounds for `(fac n) * t (n + 1)`. The lower bound is
  easy:
-/
lemma fac_mul_t_succ_pos (n : ℕ) : (fac n) * (t (n + 1)) > 0 := by
  have h1 : (fac n) > 0 := by apply fac_pos n
  have h2 : t (n + 1) > 0 := by apply t_pos (n + 1)
  positivity

/-
  For the upper bound, we proceed in a few steps. In order of appearance, we show:
  - `(fac n) * t (n + 1) ≤ 2 * (fac n) * a (n + 1)` (using `t_le_twice_a`)
  - `(fac n) * t (n + 1) ≤ 2 / (n + 1)`
  - `(fac n) * t (n + 1) < 1`
  Each builds on the previous one.
-/

lemma bound_1 (n : ℕ) (hn : n ≥ 1) :
    (fac n) * t (n + 1) ≤ 2 * (fac n) * a (n + 1) := by
  have h3 : n + 1 ≥ 1 := by linarith
  calc
    (fac n) * t (n + 1) ≤ (fac n) * (2 * (a (n + 1))) := by rel [t_le_twice_a _ h3]
    _ = _ := by algebra

-- auxiliary lemma to deduce `fac_mul_t_succ_le_2` below:
lemma aux_1 (n : ℕ) :
    (fac n) * (a (n + 1)) = 1 / (n + 1) := by
  rewrite [a_def, nat_inv_def, fac_succ]
  have h : fac n > 0 := by apply fac_pos n
  algebra

lemma bound_2 (n : ℕ) (hn : n ≥ 1) :
    (fac n) * t (n + 1) ≤ 2 / (n + 1) := by
  calc
    (fac n) * t (n + 1) ≤ 2 * (fac n) * a (n + 1) := by apply bound_1 n hn
    _ = 2 * ((fac n) * a (n + 1)) := by algebra
    _ = 2  / (n + 1) := by rewrite [aux_1 n]; algebra

-- auxiliary lemma to deduce `fac_mul_t_succ_lt_one` below:
lemma aux_2 (n : ℕ) (hn : n ≥ 2) :
    (2 : ℝ) / (n + 1) ≤ 2 / 3 := by
  have h2 : (2 : ℝ) > 0 := by numbers
  apply (mul_le_mul_left h2).mpr
  have h3 : (n : ℝ) + 1 > 0 := by linarith
  have h4 : (3 : ℝ) > 0 := by numbers
  apply (inv_le_inv h3 h4).mpr
  linarith

theorem fac_mul_t_succ_lt_one (n : ℕ) (hn : n ≥ 2) :
    (fac n) * t (n + 1) < 1 := by
  have h1 : n ≥ 1 := by linarith
  calc
    (fac n) * t (n + 1) ≤ 2 / (n + 1) := by apply bound_2 n h1
    _ ≤ 2 / 3 := by apply aux_2 n hn
    _ < 1 := by numbers



/-
  ## Part VIII: The irrationality of `e`

  Recall that we have for all `n ≥ 2`:
  - `(fac n) * t (n + 1) > 0`, by lemma `fac_mul_t_succ_pos`
  - `(fac n) * t (n + 1) < 1`, by theorem `fac_mul_t_succ_lt_one`

  We also know that:
  - `(fac n) * s (n + 1)` is integral, by theorem `isInt_fac_mul_s`

  If `e` were rational, then theorem `rationality_criterion` would give us a `n ≥ 2` such that
  - `(fac n) * e` is integral

  But since `t (n + 1) = e - s (n + 1)`, we would conclude that
  - `(fac n) * (e - s (n + 1))` is integral ??
  A contradiction with the inequalities above. Below we spell out this argument in detail.
-/


/-
  First we show that `(fac n) * t (n + 1)` is not integral (it lies strictly between 0 and 1).
-/
lemma fac_mul_t_succ_not_integral (n : ℕ) (hn : n ≥ 2) :
    ¬ isInt ((fac n) * t (n + 1)) := by
  have h1 : (fac n) * t (n + 1) < 1 := by apply fac_mul_t_succ_lt_one n hn
  have h2 : (fac n) * t (n + 1) > 0 := by apply fac_mul_t_succ_pos n
  apply no_int_between_0_and_1 h2 h1

/-
  Under the assumption that `n ≥ 2`, we have now established:
  - `(fac n) * t (n + 1)` is not integral (above)
  - `(fac n) * s (n + 1)` is integral (this is lemma `s_integrality`)
  - `t (n + 1) = e - s (n + 1)` (by lemma `t_def`)
  From this we should be able to conclude that `(fac n) * e` is not integral!
-/
lemma fac_mul_e_not_integral (n : ℕ) (hn : n ≥ 2) :
    ¬ isInt ((fac n) * e) := by
  intro he
  have hsub : (fac n) * t (n + 1) = (fac n) * e - (fac n) * s (n + 1) := by
    rewrite [t_def]; algebra
  have hs : isInt ((fac n) * s (n + 1)) := by
    apply isInt_fac_mul_s (n + 1) n (by linarith)
  have ht : isInt ((fac n) * t (n + 1)) := by
    rewrite [hsub]
    apply isInt_sub he hs
  apply fac_mul_t_succ_not_integral n hn ht




/-
  Now everything comes together!!
-/
theorem e_irrational : ¬ isRat e := by
  -- assume for the sake of contradiction `h : isRat e`
  by_contra h
  -- then `fac_mul_integral_of_rational e h` gives us a `n ≥ 2` such that `(fac n) * e` is integral
  obtain ⟨n, h1, h2⟩ := rationality_criterion e h
  -- now `fac_mul_e_not_integral n h1` gives us a contradiction with `h2`
  apply fac_mul_e_not_integral n h1
  apply h2


/-
  Let's check to make sure that no `sorry`s are left in the proof. This should print:
    `'e_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]`
  If in stead it mentions `sorryAx`, then there is still a `sorry` left somewhere...
-/
#print axioms e_irrational
