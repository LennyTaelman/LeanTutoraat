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

lemma fac_one : fac 1 = 1 := by rw [fac_succ]; rw [fac_zero]

lemma fac_two : fac 2 = 2 := by rw [fac_succ]; rw [fac_one]

lemma fac_three : fac 3 = 6 := by rw [fac_succ]; rw [fac_two]


lemma fac_pos (n : ℕ) : fac n > 0 := by
  simple_induction n with n IH
  · rewrite [fac_zero]; positivity
  · rewrite [fac_succ]; positivity

lemma fac_ne_zero (n : ℕ) : fac n ≠ 0 := by
  linarith [fac_pos n]

lemma fac_ge_one (n : ℕ) : fac n ≥ 1 := by
  linarith [fac_pos n]

lemma fac_strictly_monotone (n : ℕ) (h : n ≥ 1) : fac (n + 1) > fac n := by
  rewrite [fac_succ]
  have h1 : n + 1 > 1 := by extra
  have h2 : fac n > 0 := by apply fac_pos n
  calc
    (n + 1) * fac n > 1 * fac n := by rel [h1]
    _ = fac n := by algebra

lemma fac_gt_one (n : ℕ) (h : n ≥ 2) : fac n > 1 := by
  induction_from_starting_point n, h with k hk IH
  · rewrite [fac_two]; numbers
  · have hk' : k ≥ 1 := by linarith
    linarith [fac_strictly_monotone k hk']


lemma fac_gt_of_gt (n m : ℕ) (h1 : n ≥ m + 1) (h2 : m ≥ 1): fac n > fac m := by
  induction_from_starting_point n, h1 with k hk IH
  · apply fac_strictly_monotone m h2
  · rewrite [fac_succ]
    calc
      (k + 1) * fac k = k * fac k + fac k := by algebra
                    _ ≥ fac k := by extra
                    _ > fac m := by linarith

lemma fac_ge_of_ge (n m : ℕ) (h : m ≥ n) : fac m ≥ fac n := by
  induction_from_starting_point m, h with k hk IH
  · extra
  · have h : k + 1 ≥ 1 := by extra
    calc
      fac (k + 1) = (k + 1) * fac k := by rw [fac_succ]
      _ ≥ 1 * fac k := by rel [h]
      _ = fac k := by algebra
      _ ≥ fac n := by rel [IH]

lemma fac_ge_two (n : ℕ) (hn : n ≥ 2) : fac n ≥ 2 := by
  calc fac n ≥ fac 2 := fac_ge_of_ge 2 n hn
    _ = 2 := by rewrite [fac_two]; rfl

lemma fac_prev (n : ℕ) (h1 : n ≥ 1) : fac n = fac (n - 1) * n := by
  induction_from_starting_point n, h1 with k hk IH
  · rewrite [fac_one, fac_zero]; numbers
  · rewrite [fac_succ k]; algebra


/-
  In the proof of `fac_bound` below, it will be useful to know that `2 ^ k * fac n` is positive.
-/

lemma aux (n : ℕ) (k : ℕ) : 0 < 2 ^ k * fac n := by
  have h : fac n > 0 := by apply fac_pos
  positivity

/-
  The following is the key inequality in the proof of irrationality of `e`.
  I recommend you write out the proof in detail on paper first.
-/
theorem fac_bound (n : ℕ) (k : ℕ) (hn : n > 0) :
    fac (n + k) ≥ 2 ^ k * fac n := by
  simple_induction k with k IH
  · -- base case
    calc fac (n + 0) = 1 * fac n := by algebra
      _ ≥ 1 * fac n := by extra
  · -- inductive step
    have h1 : n + k + 1 ≥ 2 := by addarith [hn]
    have h2 : fac n > 0 := by apply fac_pos
    calc fac (n + (k + 1)) = fac (n + k + 1) := by algebra
      _ = (n + k + 1) * fac (n + k) := by rw [fac_succ]
      _ ≥ (n + k + 1) * (2 ^ k * fac n) := by rel [IH]
      _ ≥ 2 * (2 ^ k * fac n) := by rel [h1]
      _ = 2 ^ (k + 1) * fac n := by algebra


/-
  ## Part II: the term `a n := 1 / n!`
-/

/-
  We will define `e` as `∑_n 1 / n!`. There is a subtlety here:
  we have defined `fac n` as a natural number, and we want to consider
  its inverse as a real number. To avoid lots of technicalities later on,
  we separate out the transition from "natural number `n!`" to "real number `1 / n!`",
  and prove the elementary properties of this function.
-/

def nat_inv (n : ℕ) : ℝ := (n : ℝ)⁻¹

lemma nat_inv_def (n : ℕ) : nat_inv n = (n : ℝ)⁻¹ := by rfl

lemma nat_inv_one : nat_inv 1 = 1 := by
  rw [nat_inv_def]
  numbers

lemma nat_inv_pos (n : ℕ) (hn : n > 0) : nat_inv n > 0 := by
  rw [nat_inv_def n]
  positivity

lemma nat_inv_ne_zero (n : ℕ) (hn : n > 0) : nat_inv n ≠ 0 := by
  linarith [nat_inv_pos n hn]

lemma nat_inv_mul (n m : ℕ) : nat_inv (n * m) = nat_inv n * nat_inv m := by
  rewrite [nat_inv_def, nat_inv_def, nat_inv_def]
  algebra

lemma nat_inv_le (n m : ℕ) (h : n ≥ m) (hm : m > 0) : nat_inv n ≤ nat_inv m := by
  rewrite [nat_inv_def n, nat_inv_def m]
  have hn : n > 0 := by linarith
  apply inv_le_inv_of_le
  positivity
  linarith

lemma nat_inv_lt (n m : ℕ) (h : n > m) (hm : m > 0) : nat_inv n < nat_inv m := by
  rw [nat_inv_def n, nat_inv_def m]
  have hn : n > 0 := by linarith
  apply inv_lt_inv_of_lt
  positivity
  linarith

lemma nat_inv_le_one (n : ℕ) (hn : n > 0) : nat_inv n ≤ 1 := by
  rewrite [← nat_inv_one]
  apply nat_inv_le
  exact hn
  numbers

lemma nat_inv_lt_one (n : ℕ) (hn : n > 1) : nat_inv n < 1 := by
  rewrite [← nat_inv_one]
  apply nat_inv_lt
  exact hn
  numbers



/-
  Now define `a n := nat_inf fac n`, so `a n = 1 / n!`
-/

def a (n : ℕ) : ℝ := nat_inv (fac n)

lemma a_def (n : ℕ) : a n = nat_inv (fac n) := by rfl

lemma a_zero : a 0 = 1 := by
  rewrite [a_def, fac_zero, nat_inv_one]
  rfl

lemma a_one : a 1 = 1 := by
  rewrite [a_def, fac_one, nat_inv_one]
  rfl

lemma a_two : a 2 = 1 / 2 := by
  rewrite [a_def, fac_two, nat_inv_def]
  numbers

lemma a_three : a 3 = 1 / 6 := by
  rewrite [a_def, fac_three, nat_inv_def]
  numbers

lemma a_succ (n : ℕ) : a (n + 1) = a n / (n + 1) := by
  rewrite [a_def, a_def, nat_inv_def, nat_inv_def, fac_succ]
  algebra

lemma a_pos (n : ℕ) : a n > 0 := by
  rewrite [a_def]
  apply nat_inv_pos
  apply fac_pos

lemma a_le_one (n : ℕ) : a n ≤ 1 := by
  rewrite [a_def]
  apply nat_inv_le_one
  apply fac_pos

lemma a_le (n m : ℕ) (h : n ≥ m) : a n ≤ a m := by
  rw [a_def]
  apply nat_inv_le
  apply fac_ge_of_ge
  apply h
  apply fac_pos

lemma a_lt (n m : ℕ) (h : n > m) (hn : m > 0) : a n < a m := by
  rw [a_def]
  apply nat_inv_lt
  apply fac_gt_of_gt
  exact h
  linarith
  apply fac_pos

lemma fac_mul_a_eq_one (n : ℕ) : fac n * a n = 1 := by
  rewrite [a_def, nat_inv_def]
  have h : fac n ≠ 0 := by apply fac_ne_zero
  algebra

lemma a_bound_aux (n : ℕ) (k : ℕ) : (1/2) ^ k * (a n) = nat_inv (2 ^ k * fac n) := by
  rewrite [a_def, nat_inv_def, nat_inv_def]
  algebra


/-
  We can now use `fac_bound` from above to prove the following key inequality
  for `a n`. Hint: use `a_bound_aux` to rewrite this into an inequality between
  `nat_inv`'s.
-/
theorem a_bound (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    a (n + k) ≤  (1/2) ^ k * (a n) := by
  rewrite [a_bound_aux, a_def]
  apply nat_inv_le
  apply fac_bound
  positivity
  apply aux n k




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

lemma g_zero : g 0 = 0 := by rfl

lemma g_succ (n : ℕ) : g (n + 1) = g n + (1/2) ^ n := by rfl

lemma g_one : g 1 = 1 := by rw [g_succ, g_zero]; numbers

lemma g_two : g 2 = 3 / 2 := by rw [g_succ, g_one]; numbers

lemma g_three : g 3 = 7 / 4 := by rw [g_succ, g_two]; numbers

lemma g_eq (n : ℕ) : g n = 2 - 2 * (1/2) ^ n := by
  simple_induction n with n IH
  · simp; rfl
  · rewrite [g_succ]
    rewrite [IH]
    algebra


-- we can now prove the main result of this section:

theorem g_lt_2 (n : ℕ) : g n < 2 := by
  calc
    g n = 2 - 2 * (1/2) ^ n := by rewrite [g_eq]; rfl
    _ < 2 := by extra



/-
  ## Part IV: the partial sums `s n`

  Recall that `a n = 1 / n!`. We will define the number `e` through the series `e = ∑_n a n`.
  Consider the partial sums:
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
  Key bounds on s n
-/
theorem s_geometric_bound (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
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
      _ ≤ s n + (a n) * (g k) + (1/2) ^ k * a n := by rel [a_bound n k hn]
      _ = s n + (a n) * ((g k) + (1/2) ^ k) := by algebra
      _ = s n + (a n) * (g (k + 1)) := by rw [g_succ]

/-
  Using `g_lt_2` this implies that `s (n + k) < s n + 2 * (a n)`.
-/
lemma s_bound (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    s (n + k) < s n + 2 * (a n)  := by
  have h : a n > 0 := a_pos n
  calc
    _ ≤ s n + (a n) * (g k) := by apply s_geometric_bound n k hn
    _ < s n + (a n) * 2 := by rel [g_lt_2 k]
    _ = s n + 2 * (a n) := by algebra

/-
  Variant: since we eliminate `k` by replacing `n + k` with any `m` such that `m ≥ n`:
-/
lemma s_bound_variant (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ n) : s m < s n + 2 * (a n) := by
  let k := m - n
  have hk : m = n + k := by exact (Nat.sub_eq_iff_eq_add' hm).mp rfl
  calc
    s m = s (n + k)       := by rewrite [hk]; rfl
      _ < s n + 2 * (a n) := by rel [s_bound n k hn]
      _ = s n + 2 * (a n) := by algebra


/-
  Since `s` is increasing, the condition that `m ≥ n` is unnecessary!
-/

theorem s_key_bound (n m : ℕ) (hn : n ≥ 1) : s m < s n + 2 * (a n) := by
  by_cases hm : m ≥ n
  · -- either `m ≥ n`, then this is `s_bound_variant` above
    apply s_bound_variant n m hn hm
  · -- or `¬ m ≥ n`, then we have `m < n`:
    push_neg at hm
    -- now finish the proof
    have ha : a n > 0 := by apply a_pos n
    calc
      s m < s n := by apply s_monotone m n hm
        _ ≤ s n + 2 * (a n) := by extra



/-
  Application: we can use `key_bound_s` to prove that `s n` is less than `3`
  for all `n`. Indeed, taking `m = 2` we find `s n < s 2 + 2 * (a 2) = 3`.
-/
lemma s_lt_three (n : ℕ) : s n < 3 :=
  have h : 2 ≥ 1 := by numbers
  calc
    s n < s 2 + 2 * (a 2) := by exact s_key_bound 2 n h
      _ = 3 := by rw [a_two, s_two]; numbers


/-
  ## Part IV: Integrality and Rationality

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
  apply isInt_nat 2

example : isRat 2⁻¹ := by
  have h : 2 > 0 := by numbers
  apply isRat_inv_nat 2 h

example : isRat (5/8) := by
  have h5 : isRat 5 := by apply isRat_nat 5
  have h8 : isRat (8⁻¹) := by apply isRat_inv_nat 8 (by numbers)
  -- without the (_ : ℝ), lean will not know to treat 5 and 8 as real numbers
  have h : (5 : ℝ) / 8  = 5 * (8⁻¹) := by numbers
  rewrite [h]
  apply isRat_mul h5 h8

example (x : ℝ) (h : isInt x) : isInt (x ^ 2) := by
  have h2 : x ^ 2 = x * x := by algebra
  rewrite [h2]
  apply isInt_mul h h

/-
  Key integrality lemma about `a_n`
-/
lemma isInt_fac_mul_a (n m : ℕ) (h : n ≤ m) : isInt (fac m * a n) := by
  induction_from_starting_point m, h with k hk IH
  · rw [fac_mul_a_eq_one]
    apply isInt_one
  · -- bottleneck: make clear that k+1 is a nat!
    -- bottleneck: instinct should be to do rw [fac_succ] FIRST!
    have h2 : fac (k + 1) * a n = (k + 1 : ℕ) * (fac k * a n) := by
      rw [fac_succ]
      algebra
    rw [h2]
    apply isInt_nat_mul
    exact IH



/-
  Key rationality criterion. To prove that a number `x` is irrational, it
  suffices to show that `(fac N) * x` is not an integer for all `N`.

  The main reason is the following lemma, which states that if `n * x` is an
  integer, then `(fac n) * x` is also an integer. The proof uses `fac_prev` to
  express `fac n` as a product of `fac (n - 1)` and `n` (using the fact that `n ≥ 1`).
-/

lemma is_int_fac_mul_of_is_int_mul {x : ℝ} (n : ℕ) (h1 : n ≥ 1) (h : isInt (n * x)) : isInt (fac n * x) := by
  rewrite [fac_prev n h1]
  have h2 : (fac (n - 1) * n : ℕ) * x = (fac (n - 1) * (n * x)) := by algebra
  rewrite [h2]
  apply isInt_nat_mul h

/-
  Now we can prove the irrationality criterion that we wil use to establish that
  `e` is irrational. The proof has been pre-filled since it uses a few tactics
  we have not seen yet. The proof in English:

  Assume for the sake of contradiction that `x` is rational. Then there exists
  an `N > 0` such that `N * x` is an integer. By Lemma
  `is_int_fac_mul_of_is_int_mul`, we have that `(fac N) * x` is an integer,
  contradicting assumption `h`.
-/
lemma irrationality_criterion {x : ℝ} (h : ∀ N, ¬ isInt ((fac N) * x)) : ¬ isRat x := by
  by_contra h2
  obtain ⟨N, hN, hx⟩ := h2
  specialize h N
  apply is_int_fac_mul_of_is_int_mul N hN at hx
  contradiction





-- TODO: decide between (fac m) * s n and (fac m) * s (n + 1) !

lemma isInt_fac_mul_s (n : ℕ) (m : ℕ) (h : m + 1 ≥ n):
    isInt ((fac m) * s n) := by
  simple_induction n with k IH
  · rw [s_zero]; simp; apply isInt_zero
  · have h2 : (fac m) * s (k + 1) = (fac m) * s k + (fac m) * a k := by
      rewrite [s_succ]; algebra
    rewrite [h2]
    apply isInt_add
    · have h' : m + 1 ≥ k := by linarith
      apply IH h'
    · have h'' : m ≥ k := by linarith
      apply isInt_fac_mul_a k m h''






/-
  ## The number `e` as limit of the sequence `s n`

  The next part defines the number `e` as follows:
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
  `|s n| ≤ 3`, so `s n` is a bounded sequence.
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
    rel [s_lt_next n]
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
  have h2 : e < s (n+1) := by addarith [h, s_lt_next n]
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
    _ ≤ s m - e := by linarith [s_monotone' (n + 1) m hm2]
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
  ## Part V: Key bounds on the number `e`

  We now use `s_lt_e` and `e_le_of_s_le` to prove some inequalities satisfied by `e`.
-/

-- hint: `s 2 = 2`
theorem e_gt_2 : e > 2 := by
  calc
    e > s 2 := by apply s_lt_e
    _ = 2 := by apply s_two

theorem key_bound_e (n : ℕ) (hn : n ≥ 1): e ≤ s n + 2 * (a n) := by
  -- by `e_le_of_s_le` it suffices to show that `s m < s n + 2 * (a n)` for all `m`.
  apply e_le_of_s_le _
  intro m
  -- finish the proof by applying `s_key_bound`
  apply s_key_bound n m hn


/-
  Application: `e < 3`. Hint: `s 3 + 2 * (a 3) = 17/6 < 3`
-/
theorem e_lt_3 : e < 3 := by
   calc
    e ≤ s 3 + 2 * (a 3) := by apply key_bound_e; numbers
    _ < 3 := by rewrite [s_three, a_three]; numbers



/-
  ## The tail `t n` of the series

  We will now prove that e is irrational. Consider the tail

  `t n = e - s n = 1 / n! + 1 / (n+1)! + ...`

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
  linarith [s_lt_e n]

lemma t_le_twice_a (n : ℕ) (hn : n ≥ 1) : t n ≤ 2 * (a n) := by
  -- let's first spell out the definition of `t n`
  rewrite [t_def]
  have h : e ≤ s n + 2 * (a n) := by apply key_bound_e n hn
  linarith


lemma fac_mul_a_succ (n : ℕ) :
    (fac n) * (a (n + 1)) = 1 / (n + 1) := by
  rewrite [a_def, nat_inv_def, fac_succ]
  have h : fac n > 0 := by apply fac_pos n
  algebra

lemma fac_mul_t_le (n : ℕ) (hn : n ≥ 1) :
    (fac n) * t (n + 1) ≤ 2 * (fac n) * a (n + 1) := by
  have h3 : n + 1 ≥ 1 := by linarith
  calc
    (fac n) * t (n + 1) ≤ (fac n) * (2 * (a (n + 1))) := by rel [t_le_twice_a _ h3]
    _ = _ := by algebra

-- TODO: continue from here, with the above lemmas should be able

lemma fac_mul_t_le' (n : ℕ) (hn : n ≥ 1) :
    (fac n) * t (n + 1) ≤ 2 / (n + 1) := by
  calc
    (fac n) * t (n + 1) ≤ 2 * (fac n) * a (n + 1) := by apply fac_mul_t_le n hn
    _ = 2 * ((fac n) * a (n + 1)) := by algebra
    _ = 2  / (n + 1) := by rewrite [fac_mul_a_succ n]; algebra

lemma le_two_thirds (n : ℕ) (hn : n ≥ 2) :
    (2 : ℝ) / (n + 1) ≤ 2 / 3 := by
  have h2 : (2 : ℝ) > 0 := by numbers
  apply (mul_le_mul_left h2).mpr
  have h3 : (n : ℝ) + 1 > 0 := by linarith
  have h4 : (3 : ℝ) > 0 := by numbers
  apply (inv_le_inv h3 h4).mpr
  linarith

/-
  Combining `fac_mul_t_le'` and `le_two_thirds` we get that
  `(fac n) * t (n + 1) ≤ 2 / (n + 1) ≤ 2 / 3 < 1`
-/

lemma fac_mul_t_succ_lt_1 (n : ℕ) (hn : n ≥ 2) :
    (fac n) * t (n + 1) < 1 := by
  have h1 : n ≥ 1 := by linarith
  calc
    (fac n) * t (n + 1) ≤ 2 / (n + 1) := by apply fac_mul_t_le' n h1
    _ ≤ 2 / 3 := by apply le_two_thirds n hn
    _ < 1 := by numbers


/-
  We also have: `(fac n) * t (n + 1) > 0`. To prove this, establish that `fac n`
  and `t (n + 1)` are positive (using lemmas proven above), and let `positivity` conclude.
-/
lemma fac_mul_t_succ_pos (n : ℕ) : (fac n) * (t (n + 1)) > 0 := by
  have h1 : (fac n) > 0 := by apply fac_pos n
  have h2 : t (n + 1) > 0 := by apply t_pos (n + 1)
  positivity

/-
  But something that is both `< 1` and `> 0` cannot be an integer! This can be
  shown using the lemma
    `no_int_between_0_and_1 (h1 : x > 0) (h2 : x < 1) : ¬ isInt x`
-/
lemma fac_mul_t_succ_not_integral (n : ℕ) (hn : n ≥ 2) :
    ¬ isInt ((fac n) * t (n + 1)) := by
  have h1 : (fac n) * t (n + 1) < 1 := by apply fac_mul_t_succ_lt_1 n hn
  have h2 : (fac n) * t (n + 1) > 0 := by apply fac_mul_t_succ_pos n
  apply no_int_between_0_and_1 h2 h1

/-
  Under the assumption that `n ≥ 2`, we have now established:
  - `(fac n) * t (n + 1)` is not integral (this is lemma `fac_mul_t_succ_not_integral`)
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

#print axioms fac_mul_e_not_integral


lemma fac_mul_integral_of_rational (x : ℝ) (h : isRat x) :
    ∃ n : ℕ, n ≥ 2 ∧ isInt ((fac n) * x) := by
  obtain ⟨p, q, hq, hx⟩ := h

  use q
  rw [hx]
  rw [fac_div_integral q hq]
  algebra
  sorry


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
    rw [fac_div_integral q hq]
    algebra




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
