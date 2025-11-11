import Library.Basic


/- # Recap and consolidation -/

/- ## Induction with `simple_induction` and `induction_from_starting_point` -/

/-
  Recall: `simple_induction n with k IH` creates two goals:
  - a base case: prove the statement for `n = 0`
  - an inductive step: prove the statement for `n = k + 1`,
    where the induction hypothesis `IH` is that the statement holds for `n = k`
  We then need to provide proofs for the base case and the inductive step.

  The variant `induction_from_starting_point n, hn with k hk IH` creates two
  goals:
  - a base case: prove the statement for `n = C` (the value of `C` is inferred
    from the hypothesis `hn : C ≤ n`)
  - an inductive step: prove the statement for `n = k + 1`,
    where the induction hypothesis `IH` is that the statement holds for `n = k`,
    and the assumption `hk` is that `k ≥ C`
-/


/-
  Let's prove some basic inequalities about the factorial function. We define it
  by induction (or recursion). To manipulate it, you use the following two
  lemmas:
  - `fac_zero : fac 0 = 1`
  - `fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n`
  introduced below.
-/

def fac (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * fac n

lemma fac_zero : fac 0 = 1 := by rfl

lemma fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by rfl

/-
  Let's do some sanity checks to make sure this matches our expectations.
-/

example : fac 0 = 1 := by rewrite [fac_zero]; rfl

example : fac 1 = 1 := by rewrite [fac_succ]; rewrite [fac_zero]; numbers

example : fac 2 = 2 := by rewrite [fac_succ, fac_succ]; rewrite [fac_zero]; numbers

example : fac 3 = 6 := by rewrite [fac_succ, fac_succ, fac_succ]; rewrite [fac_zero]; numbers


/-
  Use induction to prove that `fac n ≥ 1` for all `n : ℕ`.
-/

lemma fac_ge_one (n : ℕ) : fac n ≥ 1 := by
  simple_induction n with k IH
  · rewrite [fac_zero]; numbers
  · rewrite [fac_succ]
    calc
      (k + 1) * fac k ≥ (k + 1) * 1 := by rel [IH]
      _ = k + 1 := by algebra
      _ ≥ 1 := by linarith

/-
  Recall: to prove a statement of the form `∃ N, ...` you can use the tactic
  `use C` to say "Let's prove that `N = C` satisfies the desired property."
-/

example (N : ℕ) : ∃ n : ℕ, fac n ≥ N := by
  use N
  simple_induction N with k IH
  · rewrite [fac_zero]; numbers
  · rewrite [fac_succ]
    calc
      (k + 1) * fac k ≥ (k + 1) * 1 := by rel [fac_ge_one k]
      _ = k + 1 := by algebra


/-
  Let's do one more inequality:
  `fac n ≥ 2 ^ n` for all `n` sufficiently large.
-/

example (n : ℕ) (h : n ≥ 4): fac n ≥ 2 ^ n := by
  induction_from_starting_point n, h with k hk IH
  · rewrite [fac_succ, fac_succ, fac_succ, fac_succ, fac_zero]; numbers
  · rewrite [fac_succ]
    have h2 : k + 1 ≥ 2 := by linarith
    calc
      (k + 1) * fac k ≥ (k + 1) * 2 ^ k := by rel [IH]
      _ ≥  2 * 2 ^ k := by rel [h2]
      _ = 2 ^ (k + 1) := by algebra


/-
  ## Mixing naturals and reals

  So far, we have mostly proven equalities and inequalities where all variables
  where either natural numbers, integers, or real numbers. Sometimes we need to
  mix them and interpret for example a natural number `n` as a *real* number.
  This requires some care!

  Lean does a lot of this handling automatically, which makes things more confusing.
  (It is not clear what goes wrong when thigns go wrong...)

  Let's make things more explicit.
-/

def nat_to_real (n : ℕ) : ℝ := n

lemma nat_to_real_def (n : ℕ) : nat_to_real n = ↑n := by rfl

/-
  We can now be very careful, and write `nat_to_real n` when we want to consider the natural
  number `n` as a real number.

  Let's prove some basic properties. General strategy:
  1) use `rewrite [nat_to_real_def]` to unfold the definition of `nat_to_real`.
  2) inspect the goal. It will contain things such as `↑n`, which means "the number `n`
       considered as a real number".
  3) the tactics `numbers`, `algebra`, and `linarith` can usually deal with these automatically.
-/

-- the image of the natural number 0 is the real number 0
lemma nat_to_real_zero : nat_to_real 0 = 0 := by rewrite [nat_to_real_def]; numbers

-- addition of naturals is compatible with addition of reals
lemma nat_to_real_add (n m : ℕ) : nat_to_real (n + m) = nat_to_real n + nat_to_real m := by
  rewrite [nat_to_real_def, nat_to_real_def, nat_to_real_def]
  algebra

-- multiplication of naturals is compatible with multiplication of reals
lemma nat_to_real_mul (n m : ℕ) : nat_to_real (n * m) = nat_to_real n * nat_to_real m := by
  rewrite [nat_to_real_def, nat_to_real_def, nat_to_real_def]
  algebra

/-
  The following is *false*! Check that you cannot prove it in the same way as the previous lemmas.
  Why is that? Because `n - m` denotes the natural number `n - m`, which is defined to be `0` if `n < m`.
-/
lemma nat_to_real_sub (n m : ℕ) : nat_to_real (n - m) = nat_to_real n - nat_to_real m := by
  rewrite [nat_to_real_def, nat_to_real_def, nat_to_real_def]
  sorry -- inspect the goal before this `sorry`. Verify that `algebra` cannot prove this.


-- inequalities of naturals are compatible with inequalities of reals
lemma nat_to_real_of_le (n m : ℕ) (h : nat_to_real n ≥ nat_to_real m) : n ≥ m := by
  rewrite [nat_to_real_def, nat_to_real_def] at h
  linarith






/-
  For example, the following example shows that the inequality of natural numbers
  is compatible with inequality of real numbers. Put your cursor before `sorry` and
  you will see that
  - you have a hypothesis `h : n ≥ m`
  - you have a goal `↑n ≥ ↑m`
  Here the uparrow in `↑n` indicates that `n` is being considered as a real number.

  Note that this is *not* an empty statement! Fortunately, `linarith` can do this
  automatically.
-/

example (n m : ℕ) (h : n ≥ m) : (n : ℝ) ≥ (m : ℝ) := by
  linarith

/-
  Sometimes `linarith` needs a hint. In the example below, first use `linarith`
  to prove that the *real* number `n` is greater than the *real* number `m`, and then let
  `linarith` do the rest
-/
example (n : ℕ) (m : ℕ) (h : n > m) (x : ℝ) : n + x > m + x := by
  have h2 : (n : ℝ) > (m : ℝ) := by linarith
  linarith


/-
  Here is another example. Let's define `nat_mul n x` inductively as:
  - `nat_mul 0 x = 0`
  - `nat_mul (n + 1) x = nat_mul n x + x`
  We have `nat_mul n x = x + x + ... + x` (with `n` terms)
-/

def nat_mul (n : ℕ) (x : ℝ) : ℝ := n * x

lemma nat_mul_def (n : ℕ) (x : ℝ) : nat_mul n x = n * x := by rfl

/-
  Let's do some basic checks
-/

lemma nat_mul_one (x : ℝ) : nat_mul 1 x = x := by rewrite [nat_mul_def]; algebra

lemma nat_mul_two (x : ℝ) : nat_mul 2 x = 2 * x := by rewrite [nat_mul_def]; algebra




/-
  We can now prove that `nat_mul n x = n * x` for all `n : ℕ` and `x : ℝ`.
-/


example (n m : ℕ) (x : ℝ) : nat_mul (n + m) x = nat_mul n x + nat_mul m x := by
  rewrite [nat_mul_def, nat_mul_def, nat_mul_def]
  algebra
