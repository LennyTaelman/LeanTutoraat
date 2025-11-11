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
  ## Mixed identities and inequalities

  So far, we have mostly proven equalities and inequalities where all variables
  where either natural numbers, integers, or real numbers. Sometimes we need to
  mix them and interpret for example a natural number `n` as a *real* number.
  This requires some care!
-/


example (n : ℕ) (m : ℕ) : (n + m : ℝ) = (n : ℝ) + (m : ℝ) := by
  algebra

example (n : ℕ) (m : ℕ) (h : n ≥ m) : (n : ℝ) ≥ (m : ℝ) := by
  linarith

/-
  Sometimes `linarith` needs a hint. In the example below, first use `linarith`
  to prove that the *real* number `n` is greater than the *real* number `m`, and then let
  `linarith` do the rest
-/
example (n : ℕ) (m : ℕ) (h : n > m) (x : ℝ) : n + x > m + x := by
  have h2 : (n : ℝ) > (m : ℝ) := by linarith
  linarith

example (n m : ℕ) (x : ℝ) : (n + m) * x = n * x + m * x := by
  algebra
