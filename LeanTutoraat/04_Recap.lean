import Library.Basic
noncomputable section

/- # Recap and consolidation -/

/- ## Induction proofs and the factorial function -/

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
  ## Halving natural numbers

  Let's start mixing natural and real numbers a bit. We introduce the function
  `halve` which sends a natural number `n` to the real number `n / 2`.
-/

def halve (n : ℕ) : ℝ := n / 2

/-
  The following lemma just spells out the definition. It allows you to use
    `rewrite [halve_def]` to replace `halve n` with its definition.
-/

lemma halve_def (n : ℕ) : halve n = n / 2 := by rfl

/-
  Now let's do some basic checks:
-/

example : halve 0 = 0 := by rewrite [halve_def]; numbers

example : halve 1 = 1 / 2 := by rewrite [halve_def]; numbers

example : halve 2 = 1 := by rewrite [halve_def]; numbers

/-
  And let's prove some simple lemma's.
-/

lemma twice_halve (n : ℕ) : 2 * (halve n) = n := by
  rewrite [halve_def]
  algebra

lemma halve_add (n m : ℕ) : halve (n + m) = halve n + halve m := by
  rewrite [halve_def, halve_def, halve_def]
  algebra

lemma halve_non_neg (n : ℕ) : halve n ≥ 0 := by
  rewrite [halve_def]
  positivity

lemma halve_le_self (n : ℕ) : halve n ≤ n := by
  rewrite [halve_def]
  linarith

lemma halve_succ (n : ℕ) : halve (n + 1) = halve n + 1 / 2 := by
  rewrite [halve_def, halve_def]
  algebra

lemma halve_zero : halve 0 = 0 := by
  rewrite [halve_def]
  numbers


-- TODO: make sure we practice using `apply` with these lemmas!!

/-
  Sometimes `linarith` needs a hint. In the example below, first use `linarith`
  to prove that the *real* number `n` is greater than the *real* number `m`,
  using
    `have h2 : (n : ℝ) < (m : ℝ) := by linarith`
  and then use `linarith` to finish the proof.
-/
lemma halve_lt (n m : ℕ) (h : n < m) : halve n < halve m := by
  rewrite [halve_def, halve_def]
  -- `linarith` cannot finish this without a hint. We first establish that `(n : ℝ) < (m : ℝ)`
  have h2 : (n : ℝ) < (m : ℝ) := by linarith
  linarith

lemma halve_le (n m : ℕ) (h : n ≤ m) : halve n ≤ halve m := by
  rewrite [halve_def, halve_def]
  have h2 : (n : ℝ) ≤ (m : ℝ) := by linarith
  linarith


/-
  Optional challenge!
-/
lemma halve_to_inf (x : ℝ) : ∃ n : ℕ, x ≤ halve n := by
  sorry
