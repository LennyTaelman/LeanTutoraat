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
  Geometric series
-/

def geom (c : ℝ) (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => c ^ n + geom c n

lemma geom_zero (c : ℝ) : geom c 0 = 0 := by rfl

lemma geom_succ (c : ℝ) (n : ℕ) :
    geom c (n + 1) = c ^ n + geom c n := by rfl

/-
  Sanity checks
-/

lemma geom_one (c : ℝ) : geom c 1 = 1 := by
  rewrite [geom_succ, geom_zero]; algebra

lemma geom_two (c : ℝ) : geom c 2 = 1 + c := by
  rewrite [geom_succ, geom_one]; algebra

lemma geom_three (c : ℝ) : geom c 3 = 1 + c + c ^ 2 := by
  rewrite [geom_succ, geom_two]; algebra

/-
  The main result, version 1:
-/

lemma geom_series (c : ℝ) (n : ℕ) : (1 - c) * geom c n = 1  - c ^ n := by
  simple_induction n with k IH
  · rewrite [geom_zero]; algebra
  · rewrite [geom_succ]
    calc
      (1 - c) * (c ^ k + geom c k) = (1 - c) * c ^ k + (1 - c) * geom c k := by algebra
      _ = 1 - c ^ (k + 1) := by rewrite [IH]; algebra

/-
  Version 2, probably more familiar:
-/

lemma geom_series' (c : ℝ) (n : ℕ) (h : 1 - c ≠ 0) : geom c n = (1 - c ^ n) / (1 - c) := by
  simple_induction n with k IH
  · rewrite [geom_zero]; algebra
  · rewrite [geom_succ, IH]; algebra

/-
  ## Mixing naturals and reals

  So far, we have mostly proven equalities and inequalities where all variables
  where either natural numbers, integers, or real numbers. Sometimes we need to
  mix them and interpret for example a natural number `n` as a *real* number.
  This requires some care!


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
