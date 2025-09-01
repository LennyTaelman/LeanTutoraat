/- Copyright (c) Lenny Taelman, 2025. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Library.Basic

math2001_init


/- # First steps using Lean -/


/-
  ## A first example of a Lean proof

  First we are going to have a look at an example proof. We will show a form of the
  Cauchy--Schwarz inequality. It states that for vectors `v₁ = (x₁, y₁)` and
  `v₂ = (x₂, y₂)`, we have that `(v₁ · v₂)² ≤ (v₁ · v₁) (v₂ · v₂)`.

  Here is the proof in Lean:
-/


example (x₁ y₁ x₂ y₂ : ℝ) : (x₁ * y₂ + x₂ * y₁) ^ 2 ≤ (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) := by
  apply le_of_sub_nonneg
  have h : (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) - (x₁ * y₂ + x₂ * y₁) ^ 2 = (x₁ * x₂ - y₁ * y₂) ^ 2 := by
    algebra
  rewrite [h]
  apply sq_nonneg


/-
  And here is a line-by-line translation into English.

  Let `x₁, y₁, x₂, y₂` be real numbers.  Then `(x₁ * y₂ + x₂ * y₁) ^ 2 ≤ (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2)`:
    It suffices to show that `0 ≤ (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) - (x₁ * y₂ + x₂ * y₁) ^ 2`.
    We first show that  `(x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) - (x₁ * y₂ + x₂ * y₁) ^ 2 = (x₁ * x₂ - y₁ * y₂) ^ 2`:
      This follows from basic algebra.
    Using this, we can rewrite our goal as `0 ≤ (x₁ * x₂ - y₁ * y₂) ^ 2`.
    But this is true, because the square of a real number is always non-negative.

  Now move your cursour around in the Lean proof to see what happens in the right panel.

  The things before `⊢` tell us what we *have*, and the things after `⊢` tell us what we *want*.
  For example, at the start of the proof, before the first `apply`:
    - we *have* that `x₁`, `y₁`, `x₂` and `y₂` are real numbers.
    - we *want* to show that `(x₁ * y₂ + x₂ * y₁) ^ 2 ≤ (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2)`. This is
      called the *goal*.
  The commands such as `apply`, `have`, `rewrite` are called *tactics*. They are used to
  construct a proof. In the right panel you can keep track of your progress as the proof is being
  built.
-/





/-
  ## Basic identities using `numbers` and  `algebra`

  You'll now write some proofs yourself. The first two tactics prove
  trivial identities of two different kinds:
  - `numbers` proves purely numerical equalities (without variables)
  - `algebra` proves purely algebraic equalities
-/

example : 1 + 1 = 2 := by
  numbers

-- Let `a` and `b` be real numbers. Then `(a + b) * (a - b) = a ^ 2 - b ^ 2`.
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  algebra


/-
  In the following examples, the tactic `sorry` tells Lean to skip the proof
  and move on to the next example. The user is saying "Sorry, I'll prove this later!".

  Replace `sorry` with a correct one-tactic proof in the following examples
-/

example : 3 ^ 2 + 4 ^ 2 = 5 ^ 2 := by
  sorry

example (a : ℤ) : (a + 1) ^ 3 = a ^ 3 + 3 * a ^ 2 + 3 * a + 1 := by
  sorry

example (a : ℚ) : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * b * c + 2 * c * a := by
  sorry

example : (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9) ^ 2 = 2025 := by
  sorry

/-
  Try the next two examples. What happens? Why?
-/

example : 4 ^ 2 + 5 ^ 2 = 6 ^ 2 := by
  sorry

example (x : ℝ) : x / x = 1 := by
  sorry


/-
  ## Substituting with `rewrite`

  If you *have* a hypothesis `h` of the form `a = b`,
  then the tactic `rewrite [h]` looks for an `a` in the goal, and replaces it with `b`.

  Here is an example. Let `x` be a real number and assume `x = 1`. Then `2 * x = 2`.
-/
example (x : ℝ) (h : x = 1) : 2 * x = 2 := by
  rewrite [h] -- Replace `x` by `1`, new goal is `2 * 1 = 2`
  numbers


/-
  Now do a few examples yourself. Replace `sorry` with a correct proof.
-/

-- Let `n` be a natural number and assume `n = 2`. Then `n ^ 4 = 16`.
example (n : ℕ) (h : n = 2) : n ^ 4 = 16 := by
  rw [h]
  numbers

-- Let `a` and `b` be real numbers and assume `a = b`. Then `(a + b) ^ 2 = 4 * a ^ 2`.
example (a b : ℝ) (h : a = b) : (a + b) ^ 2 = 4 * a ^ 2 := by
  rewrite [h]
  algebra


example (a b : ℝ) (h1 : a = 1) (h2 : b = -2) : (a + b) ^ 2 = 1 := by
  rewrite [h1]
  rewrite [h2]
  numbers

example (x y : ℝ) (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
  rewrite [h2]
  rewrite [h1]
  numbers


/-
  Sometimes you have a hypothesis of the form `h : a = b` and want to replace
  `b` with `a` in stead of `a` with `b`. You can do this with the tactic `rewrite [← h]`.

  To type the `←` you type `\l ` (backslash, ell, space), with l for left.
-/

example (x y z : ℚ) (h : x + y = z) : z ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  rewrite [← h]
  algebra

-- replace `sorry` with a correct proof
example (x y : ℝ) (h1 : x + 1 = y) (h2 : x = 0) : y = 1 := by
  sorry


/-
  ## Substituting with a lemma

  In Lean, we write `exp x` for `e ^ x`. (Note that no parenthesis as in
  `exp(x)` are needed.)

  The lemma `exp_add` states that `exp (a + b) = exp a * exp b` for all real numbers `a` and `b`.
  Now the command `rewrite exp_add` looks for the pattern `exp (_ + _)` in the
  goal and replaces it with `exp _ * exp _`.
-/

-- TODO: delab rexp to exp (or redefine `exp`), include Real and exp in Library.Basic.
open Real

example (a b : ℝ) (h1 : exp a = 2) : exp (a + b) = 2 * exp b := by
  rewrite [exp_add]
  rewrite [h1]
  algebra

example (x y z : ℝ) : exp (x + y + z) = exp x * exp y * exp z := by
  rewrite [exp_add]
  rewrite [exp_add]
  algebra

/-
  Let's add two more lemmas to the mix. You can now use:
  - `exp_add : exp (a + b) = exp a * exp b`
  - `exp_zero : exp 0 = 1`
  - `two_mul : 2 * a = a + a`
-/

example (x : ℝ) : exp (2 * x) = (exp x) ^ 2 := by
  rewrite [two_mul]
  rewrite [exp_add]
  algebra

example (x y : ℝ) (h : x + y = 0) : (exp x) * (exp y) = 1 := by
  rewrite [← exp_add]
  rewrite [h]
  rewrite [exp_zero]
  numbers







-- rewrite at



example (x a b : ℕ) (h1 : x + 0 = a) (h2 : x = b) : a = b := by
  rewrite [add_zero] at h1
  rewrite [h1] at h2
  rewrite [h2]
  rfl







-- let's also do one with groups...

/-
  This one reads: "Let `G` be a group and `a` and `b` elements of `G`.
  Show that `(a * b)⁻¹ = b⁻¹ * a⁻¹`." This is the "socks and shoes" law.

  Hint: to write `a⁻¹` type `a\inv`

  Some useful lemmas (axioms of a group):
    `mul_assoc a b c : (a * b) * c = a * (b * c)`
    `mul_right_inv a : a * a⁻¹ = 1`
    `mul_left_inv a : a⁻¹ * a = 1`
    `mul_one a : a * 1 = a`
    `one_mul a : 1 * a = a`
-/


example [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- it suffices to show that (b⁻¹ * a⁻¹) * (a * b) = 1
  apply inv_eq_of_mul_eq_one_left
  -- now finish the proof with a series of rewrites
  rw [mul_assoc]
  rw [←mul_assoc a⁻¹]
  rw [mul_left_inv]
  rw [one_mul]
  rw [mul_left_inv]
