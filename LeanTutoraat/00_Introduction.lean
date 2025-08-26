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
-/

example (x y u v : ℝ) : (x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by

  /-
    Place your cursor here, and look in the right panel. The things before `⊢` tell us what
    we *have*, and the things after `⊢` tell us what we *want* to prove. In this case:

    - we *have* that `x`, `y`, `u` and `v` are real numbers.
    - we *want* to show that `(x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2)`.

    The thing that we *want* is called the *goal*. We will prove it by executing a number of
    commands that are called *tactics*.
  -/

  apply le_of_sub_nonneg

  /-
    Note that if you place your cursor here, the goal has changed! What happened?
    Well, the lemma `le_of_sub_nonneg` (which is proven somewhere in Lean's library of lemmas)
    states that `a ≤ b` follows from `0 ≤ b - a`. Applying this lemma we now have transformed our
    goal from `a ≤ b` to `0 ≤ b - a`.
  -/

  have h : (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2 = (x * v - y * u) ^ 2 := by algebra

  /-
    Now the goal is unchanged, but we *have* something new:
    `h : (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2 = (x * v - y * u) ^ 2`
    Namely, we have the hypothesis `h` that we can now use in the proof.
  -/

  rw [h]

  /-
    What happened? Well we wanted to show `0 ≤ a - b`, and we used the hypothesis `a - b = c` to
    rewrite (`rw`) the goal into `0 ≤ c`.
  -/

  apply sq_nonneg

  /-
    The `No goals` message meansn that we have proved our goal. We did this by applying the lemma
    `sq_nonneg` which states that `a ^ 2 ≥ 0` for all real numbers `a`.
  -/

/-
  Here is the same proof without all the annoying comments ;-)
-/

example (x y u v : ℝ) : (x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by
  apply le_of_sub_nonneg
  have h : (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2 = (x * v - y * u) ^ 2 := by ring
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
