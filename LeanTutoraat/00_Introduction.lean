/- Copyright (c) Lenny Taelman, 2025. -/

import Mathlib.Data.Real.Basic
import Library.Basic

-- math2001_init


/- # First steps using Lean -/


/-
  # An example proof

  First we are going to have a look at an example proof, without going
  into the syntactic details. You'll just move your cursor around in the proof
  to see what happens in the window on the right.

  Note: the green text between `/-` and `-/` or after a `--` are comments for you. They
  are ignored by Lean.

  The example below proves  a form of the Cauchy--Schwarz inequality.
-/

example (x y u v : ℝ) : (x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by

  /-
    Place your cursor here, and look in the right panel. It tells us we have 1 goal to prove, and
    then specifies what the goal is.The things before `⊢` tell us what
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

  have h : (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2 = (x * v - y * u) ^ 2 := by algebra

  /-
    Now the goal is unchanged, but we *have* something new:
    `h : (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2 = (x * v - y * u) ^ 2`
    Namely, we have the hypothesis `h` that we can now use in the proof. We can use it because
    we have proven it using the `algebra` tactic which automatically proves algebraic identities.
  -/

  rw [h]

  /-
    What happened? Well we wanted to show `0 ≤ a - b`, and we used the hypothesis `a - b = c` to
    replace (rewrite or `rw`) `a - b` with `c`.
  -/

  apply sq_nonneg

  /-
    The `No goals` message means that we are done! We finished the proof by applying the lemma
    `sq_nonneg` which states that `a ^ 2 ≥ 0` for all real numbers `a`.
  -/

  done




/-
  Here is the same proof without all the annoying comments ;-)
-/

example (x y u v : ℝ) : (x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by
  apply le_of_sub_nonneg
  have h : (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2 = (x * v - y * u) ^ 2 := by algebra
  rw [h]
  apply sq_nonneg

/-
  And here is the same proof in human language:

  We will show that `(x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2)`.
    It suffices to show that `0 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2`.
    By algebra, the right hand side equals `(x * v - y * u) ^ 2`.
    So it suffices to show that `0 ≤ (x * v - y * u) ^ 2`.
    But this is true, because the square of a real number is always non-negative.
-/
