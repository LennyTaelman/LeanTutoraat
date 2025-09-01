/- Copyright (c) Lenny Taelman, 2025. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic
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
-/


/-
  Now move your cursour around in the Lean proof to see what happens in the right panel.

  The things before `⊢` tell us what we *have*, and the things after `⊢` tell us what we *want*.
  For example, at the start of the proof:
    - we *have* that `x₁`, `y₁`, `x₂` and `y₂` are real numbers.
    - we *want* to show that `(x₁ * y₂ + x₂ * y₁) ^ 2 ≤ (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2)`. This is
      called the *goal*.
  The commands such as `apply`, `have`, `rewrite` are called *tactics*, they are used to
  construct a proof. In the right panel you can keep track of your progress as the proof is being
  built.
-/





/-
  ## Your first Lean proofs

  You'll now write some proofs yourself, using solely the `rewrite` command.

  If `h` is a hypothesis of the form `a = b`
  then the tactic `rewrite [h]` looks for an `a` in the goal, and replaces it with `b`.

  Here is an example:
-/

example (x y z : ℝ) (h1 : x = y) (h2 : y = z) : x = z := by
  rewrite [h1] -- Replace `x` by `y`, new goal is `y = z`
  rewrite [h2] -- Replace `y` by `z`, new goal is `z = z`
  rfl -- the goal is true by reflexivity of equality


/-
  Sometimes you have a hypothesis of the form `h : a = b` and want to replace
  `b` with `a` in a goal. You can do this with the tactic `rewrite [← h]`.

  To type the `←` you type `\l ` (backslash, ell, space), with l for left.
-/

example (x y : ℝ) (h : 1 = x) : y + x = y + 1 := by
  rewrite [← h]
  rfl


/-
  Rewriting with a lemma

  In the following example, `rewrite [h]` turns the goal into `y + 1 = 1 + y`.
  This is not something that `rfl` will prove, since it requires a proof! Fortunately,
  Lean comes with a bunch of useful lemmas that have been proven already and can be used here.
  In particular, it has the lemma `add_comm` which states that `a + b = b + a`.

  Try `rewrite [add_comm]` to see what happens.
-/

example (x y : ℝ) (h : x = 1) : y + x = 1 + y := by
  rewrite [h]
  rewrite [add_comm]
  rfl


/-
  In this example, you can use the following lemmas:
   `add_comm a b : a + b = b + a`
   `add_zero a : a + 0 = a`
   `zero_add a : 0 + a = a`
-/






/-
  Rewriting with a lemma and explicit parameters

-/




-- rewriting at hypotheses



-- rewriting with lemmas

example (x a b : ℕ) (h1 : x + 0 = a) (h2 : x = b) : a = b := by
  rewrite [add_zero] at h1
  rewrite [h1] at h2
  rewrite [h2]
  rfl




/-
  You can use the following lemmas:
    `add_assoc a b c : (a + b) + c = a + (b + c)`
    `add_comm a b : a + b = b + a`
    `mul_add a b c : a * (b + c) = a * b + a * c`
    `mul_one a : a * 1 = a`
-/

example (a b c : ℝ) : (a + b) + c = (a + c) + b := by
  rewrite [add_assoc]
  rewrite [add_comm b c]
  rewrite [add_assoc]
  rfl

example (a b c : ℝ) : (a + b) + c = b + (c + a) := by
  rw [add_comm a b]
  rw [add_assoc]
  rw [add_comm a c]

example (a b c : ℝ) : (a + b) * c = c * b + c * a := by
  rw [add_mul]
  rw [add_comm]
  rw [mul_comm b c]
  rw [mul_comm a c]




/-
  If you want a challenge, try proving the following basic algebraic identity.
  On top of the above, you can also use the lemmas
  `sq a : a ^ 2 = a * a`
  `two_mul a : 2 * a = a + a`
-/

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  sorry


/-
  Fortunately, Lean provides many forms of automation so that you don't need to
  waste your time proving simple algebraic identities using long sequences of
  rewrites.
  Try replacing the word `sorry` with the command `algebra`.
-/
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  sorry




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
