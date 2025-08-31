/- Copyright (c) Lenny Taelman, 2025. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic
import Library.Basic

open Lean PrettyPrinter Delaborator SubExpr

@[delab app.HAdd.hAdd]
def delabAddWithParens : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 6)

  let lhs := e.getArg! 4
  let rhs := e.getArg! 5

  guard (lhs.isAppOfArity ``HAdd.hAdd 6)

  let lhsStx ← delab lhs
  let rhsStx ← delab rhs
  `(($lhsStx) + $rhsStx)

@[delab app.HMul.hMul]
def delabMulWithParens : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 6)

  let lhs := e.getArg! 4
  let rhs := e.getArg! 5

  guard (lhs.isAppOfArity ``HMul.hMul 6)

  let lhsStx ← delab lhs
  let rhsStx ← delab rhs
  `(($lhsStx) * $rhsStx)

math2001_init


/- # First steps using Lean -/


/-
  ## A first example of a Lean proof

  First we are going to have a look at an example proof, without going
  into the syntactic details. You'll just move your cursor around in the proof
  to see what happens in the window on the right.

  Note: the green text between `/-` and `-/` or after a `--` are comments for you. They
  are ignored by Lean.

  The example below proves a form of the Cauchy--Schwarz inequality.
-/

example (x y u v : ℝ) : (x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by

  /-
    Place your cursor here, and look in the right panel. It tells us we have 1 goal to prove, and
    then specifies what the goal is. The things before `⊢` tell us what
    we *have*, and the things after `⊢` tell us what we *want*. In this case:

    - we *have* that `x`, `y`, `u` and `v` are real numbers.
    - we *want* to show that `(x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2)`.

    We try to obtain what we want by executing a number of commands that are called *tactics*.
  -/

  apply le_of_sub_nonneg

  /-
    Note that if you place your cursor after the `apply` command, the goal has changed!
    The lemma `le_of_sub_nonneg` (which is proven somewhere in Lean's library)
    states that `a ≤ b` follows from `0 ≤ b - a`. Applying this lemma we now have transformed our
    goal from `a ≤ b` to `0 ≤ b - a`.
  -/

  have h : (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2 = (x * v - y * u) ^ 2 := by
    algebra

  /-
    Now the goal is unchanged, but we *have* something new:
    `h : b - a = (x * v - y * u) ^ 2`
    This is a new fact `h` that we can now use in the proof. We can use it because
    we have proven it using the `algebra` tactic which automatically proves algebraic identities.
  -/

  rewrite [h]

  /-
    What happened? Well we wanted to show `0 ≤ b - a`, and we used the hypothesis `h` to
    replace  `b - a` with `(x * v - y * u) ^ 2`.
  -/

  apply sq_nonneg

  /-
    The `No goals` message means that we are done! We finished the proof by applying the library
    lemma `sq_nonneg` which states that squares of real numbers are non-negative.
  -/





/-
  Here is the same proof without all the annoying comments ;-)
-/

example (x y u v : ℝ) : (x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by
  apply le_of_sub_nonneg
  have h : (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2 = (x * v - y * u) ^ 2 := by
    algebra
  rewrite [h]
  apply sq_nonneg

/-
  And here is the same proof in human language:

  We will show that `(x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2)`:
    It suffices to show that `0 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2`.
    We now show that the right hand side equals `(x * v - y * u) ^ 2`:
      This follows from basic algebra.
    So it suffices to show that `0 ≤ (x * v - y * u) ^ 2`.
    But this is true, because the square of a real number is always non-negative.
-/




def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k

example (n₁ n₂ : ℕ) (h₁ : IsEven n₁) (h₂ : IsEven n₂) : IsEven (n₁ + n₂) := by
  unfold IsEven at *
  obtain ⟨k₁, h₁'⟩ := h₁
  obtain ⟨k₂, h₂'⟩ := h₂
  use k₁ + k₂
  rw [h₁']
  rw [h₂']
  algebra


/-
  ## Your first Lean proof

   Let's do some `rw` proofs inspired by the NNG!

-/

example (x y z : ℝ) (h1 : x = y) (h2 : y = z) : x = z := by
  rw [h1] -- Goal is now: y = z
  rw [h2] -- Goal becomes z = z, which Lean accepts as proven


-- reverse rewriting

-- rewriting at hypotheses


example (x a b : ℕ) (h1 : x + 0 = a) (h2 : x = b) : a = b := by
  rw [add_zero] at h1
  rw [h1] at h2
  rw [h2]


/-
 - `rw [← h]`
 - `rw [h1, h2]`
 - `rw [add_assoc]` vs `rw [add_assoc a b c]`
 - `rw [h1] at h2`
-/


-- rewriting with lemmas

/-
  You can use the following lemmas:
    `add_assoc a b c : (a + b) + c = a + (b + c)`
    `add_comm a b : a + b = b + a`
    `mul_add a b c : a * (b + c) = a * b + a * c`
    `mul_one a : a * 1 = a`
    `sq a : a ^ 2 = a * a`
-/

example (a b c : ℝ) : (a + b) + c = (a + c) + b := by
  rw [add_assoc]
  rw [add_comm b c]
  rw [add_assoc]

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


  sorry
