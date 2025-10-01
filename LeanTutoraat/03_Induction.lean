/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

tutoraat_init

namespace Nat



/-
  Say we want to prove something for all `n : ℕ` by induction.

  The tactic `simple_induction n with k IH` creates two goals:
  - a base case: prove the statement for `n = 0`
  - an inductive step: prove the statement for `n = k + 1`,
    where the induction hypothesis `IH` is that the statement holds for `n = k`
  We then need to provide proofs for the base case and the inductive step.
-/


-- Here is a simple example. Replace all the `sorry`s with proofs.

example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case: ⊢ 2 ^ 0 ≥ 0 + 1
    sorry
  · -- inductive step: ⊢ 2 ^ (k + 1) ≥ (k + 1) + 1
    -- note the new hypothesis `IH`
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by sorry
      _ ≥ 2 * (k + 1) := by sorry
      _ = (k + 1 + 1) + k := by sorry
      _ ≥ k + 1 + 1 := by sorry


-- Now prove Bernoulli's inequality:

example (x : ℝ) (n : ℕ) (h : x ≥ 0) : (1 + x) ^ n ≥ 1 + n * x := by
  simple_induction n with k IH
  · -- base case: ⊢ (1 + x) ^ 0 ≥ 1 + 0 * x
    -- hint: use the tactic `simp` to do some trivial simplifications first
    sorry
  · -- inductive step: ⊢ (1 + x) ^ (k + 1) ≥ 1 + (k + 1) * x
    calc (1 + x) ^ (k + 1) = (1 + x) * (1 + x) ^ k := by algebra
      _ ≥ (1 + x) * (1 + k * x) := by rel [IH]
      _ = 1 + (k + 1) * x +  k * x ^ 2 := by algebra
      _ ≥ 1 + (k + 1)  * x := by extra


-- Note: in the right window pane you may have seen expressions like `↑k`. These
-- indicate that the natural number `k` is being considered as a real number.


/-
  Now give your own inductive proof for the following statement.
  To typeset the dots for base and inductive case, use `\.`
-/

example (n : ℕ) : n ^ 2 ≥ n := by
  sorry


/-
  Sometimes we want to prove something for all n ≥ C,
  and hence want to start induction at n = C.

  If `n` is a natural number and `hn` the hypothesis that `n ≥ C`,
  then the tactic `induction_from_starting_point n, hn with k hk IH`
  creates two goals:
  - a base case: prove the statement for `n = C`
  - an inductive step: prove the statement for `n = k + 1`,
    where the induction hypothesis `IH` is that the statement holds for `n = k`
-/

example (n : ℕ) (hn : 2 ≤ n) : 3 ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc 3 ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by algebra
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by algebra
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example (n : ℕ) (hn : n ≥ 2) : 2 ^ n ≥ n ^ 2 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    sorry
  · -- inductive step
    sorry



-- TODO: add examples with ∑ over {0..n}

/- # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  sorry

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  sorry

example : ∃ C : ℕ, ∀ n : ℕ, n ≥ C → 3 ^ n ≥ 2 ^ n + 100 := by
  sorry


/- # Finite sums -/


/-
  We now show that for every `n : ℕ` we have
  `1 + 2 + 4 + ... + 2 ^ (n - 1) = 2 ^ n - 1`
  First we define the left-hand side as a function
  `g : ℕ → ℝ` which maps `n` to `1 + 2 + 4 + ... + 2 ^ (n - 1)`.
-/

def c (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => c n + 2 ^ n

/-
  You can ignore the precise form of the definition. All you need to know is
  that `c n` is a real number, and that it satisfies the following two lemmas:
-/

lemma c_zero : c 0 = 0 := by rfl

lemma c_succ (n : ℕ) : c (n + 1) = c n + 2 ^ n := by rfl



example (n : ℕ) : c n = 2 ^ n - 1 := by
  simple_induction n with k IH
  · -- base case: ⊢ c 0 = ...
    rw [c_zero]
    numbers
  · -- inductive step: ⊢ c (k + 1) = ...
    rw [c_succ]
    rw [IH]
    algebra






/-
  The code below defines s1 : ℕ → ℕ recursively. We have
  s1 n = 1 + 2 + ... + n
-/

def s1 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => (s1 n) + (n + 1)


/-
  Again you can ignore the definition above, you'll only use the following lemmas:
-/

lemma s1_zero : s1 0 = 0 := by rfl

lemma s1_succ (n : ℕ) : s1 (n + 1) = s1 n + (n + 1) := by rfl

/-
  We now prove that `s1 n = n * (n + 1) / 2`. We state it as
  `2 * s1 n = n * (n + 1)` to avoid having to deal with division in `ℕ`.
-/


example (n : ℕ) : 2 * s1 n = n * (n + 1) := by
  simple_induction n with k IH
  · -- base case: ⊢ s1 0 = ...
    rw [s1_zero]
  · -- inductive step: ⊢ s1 (k + 1) = ...
    rw [s1_succ]
    calc
      2 * (s1 k + (k + 1)) = 2 * s1 k + 2 * (k + 1) := by algebra
      _ = k * (k + 1) + 2 * (k + 1) := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) := by algebra

/-
  Consider s2 n = 1 + 2^2 + 3^2 + ... + n^2.
-/

def s2 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => (s2 n) + (n + 1) ^ 2

lemma s2_zero : s2 0 = 0 := by rfl

lemma s2_succ (n : ℕ) : s2 (n + 1) = s2 n + (n + 1) ^ 2 := by rfl


example (n : ℕ) : 6 * s2 n = n * (n + 1) * (2 * n + 1) := by
  simple_induction n with k IH
  · -- base case: s2 0 = ...
    rw [s2_zero]
  · -- inductive step: s2 (k + 1) = ...
    rw [s2_succ]
    calc
      6 * (s2 k + (k + 1) ^ 2) = 6 * s2 k + 6 * (k + 1) ^ 2 := by algebra
      _ = k * (k + 1) * (2 * k + 1) + 6 * (k + 1) ^ 2 := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) := by algebra



def s3 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => (s3 n) + (n + 1) ^ 3

lemma s3_zero : s3 0 = 0 := by rfl

lemma s3_succ (n : ℕ) : s3 (n + 1) = s3 n + (n + 1) ^ 3 := by rfl


/-
  Let us prove that s2 n ≥ n^3 / 3.
-/


example (n : ℕ) : 3 * s2 n ≥ n ^ 3 := by
  simple_induction n with k IH
  · -- base case: s2 0 ≥ 0
    rw [s2_zero]
    numbers
  · -- inductive step: s2 (k + 1) ≥ (k + 1) ^ 3 / 3
    rw [s2_succ]
    calc
      3 * (s2 k + (k + 1) ^ 2) = 3 * s2 k + 3 * (k + 1) ^ 2 := by algebra
      _ ≥ k ^ 3 + 3 * (k + 1) ^ 2 := by rel [IH]
      _ = k ^ 3 + 3 * k ^ 2 + 3 * k + 1 + (3 * k + 2) := by algebra
      _ ≥ k ^ 3 + 3 * k ^ 2 + 3 * k + 1 := by extra
      _ = (k + 1) ^ 3 := by algebra


/-
  Challenge: prove the beautiful formula s3 n  = (s1 n) ^ 2.
  E.g. 2025 = 1^3 + 2^3 + ... + 9^3 = (1 + 2 + ... + 9)^2
-/

-- TODO: bah, no good way of doing this without first establihsing formula for s1
