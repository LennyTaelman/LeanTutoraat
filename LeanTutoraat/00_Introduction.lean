import Library.Basic
open Tutoraat

/- # First steps using Lean -/

/-
  You'll work through this file gradually from top to bottom, at your own pace.

  The text written in green (such as these lines here) is only for you, it will be
  ignored by Lean.
-/


/-
  ## A first example of a Lean proof

  First we are going to have a look at an example proof, without worrying too
  much about the details.

  Here is what the statement and proof look like in Lean:
-/

example (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  apply le_of_diff_nonneg
  have h : 2 * (x ^ 2 + y ^ 2) - (x + y) ^ 2 = (x - y) ^ 2 := by
    algebra
  rewrite [h]
  apply zero_le_sq

/-
  And here is a line-by-line translation into English.

  Let `x` and `y` be real numbers. Then `(x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2)`. Proof:
    It suffices to show that `0 ≤ 2 * (x ^ 2 + y ^ 2) - (x + y) ^ 2`.
    We claim that `2 * (x ^ 2 + y ^ 2) - (x + y) ^ 2 = (x - y) ^ 2`. Proof:
      This follows from basic algebra.
    Using the claim, we can rewrite the goal as `0 ≤ (x - y) ^ 2`.
    But this is true, because the square of a real number is always non-negative.

  Now move your cursor around in the Lean proof to see what happens in the right panel.

  At any point in the proof, the things before `⊢` tell us what we *have*, and
  the things after `⊢` tell us what we *want*.

  For example, if you place your cursor before the first `apply`, you will see that:
    - we *have* that `x` and `y` are real numbers.
    - we *want* to show that `(x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2)`. This is our *goal*.
  If you place it immediately after the first `apply`, then
    - we still *have* that `x` and `y` are real numbers.
    - we now *want* to show that 0 ≤ 2 * (x ^ 2 + y ^ 2) - (x + y) ^ 2.
  After the last `apply` you'll see "No goals", indicating that the proof is complete.

  The commands such as `apply`, `have`, `rewrite` are called *tactics*. They are used to
  construct a proof. You can hover your mouse over a tactic to obtain a short description.
-/





/-
  ## Basic identities using the tactics `numbers` and  `algebra`

  You'll now write some proofs yourself. The first two tactics prove
  trivial identities of two different types:
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

example (a b c : ℚ) : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * b * c + 2 * c * a := by
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
  Indeed, if we add `x ≠ 0` to what we have, then `algebra` can prove `x / x = 1`.
-/

example (x : ℝ) (h : x ≠ 0) : x / x = 1 := by
  sorry

/-
  ## Substituting with `rewrite`

  If you *have* a hypothesis `h` of the form `a = b`,
  then the tactic `rewrite [h]` looks for an `a` in the goal, and replaces it with `b`.

  Here is an example. It states:
    Let `x` be a real number and assume `x = 1`. Then `2 * x = 2`.
  Move your cursor around in the Lean proof to see what happens in the right panel.
-/
example (x : ℝ) (h : x = 1) : 2 * x = 2 := by
  rewrite [h] -- Replace `x` by `1`, new goal is `2 * 1 = 2`
  numbers


/-
  Now do a few examples yourself. Replace `sorry` with a correct proof.
-/

-- Let `n` be a natural number and assume `n = 2`. Then `n ^ 4 = 16`.
example (n : ℕ) (h : n = 2) : n ^ 4 = 16 := by
  sorry

example (a b : ℝ) (h : a = 5 * b) : (a + b) ^ 2 = 36 * b ^ 2 := by
  sorry

example (a b : ℝ) (h1 : a = 1) (h2 : b = -2) : (a + b) ^ 2 = 1 := by
  sorry

example (x y : ℝ) (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
  sorry


/-
  Sometimes you have a hypothesis of the form `h : a = b` and want to replace
  `b` with `a` in stead of `a` with `b`. You can do this with the tactic `rewrite [← h]`.

  To type the `←` you type `\leftarrow ` or simply `\l `.
  Try it here, type `← h`:
-/

example (x y z : ℚ) (h : x + y = z) : z ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  rewrite [← h]
  algebra

-- replace `sorry` with a correct proof
example (x y : ℝ) (h1 : x + 1 = y) (h2 : x = 0) : y = 1 := by
  sorry


/-
  ## Using `rewrite` with a Lean lemma

  In Lean, we write `sin x` and `cos x` in stead of sin(x) and cos(x). In the exercises
  below, we will *use* a number of (already proven) lemmas:
  `sin_zero : sin 0 = 0`
  `sin_pi : sin π = 0`
  `cos_zero : cos 0 = 1`
  `cos_pi : cos π = -1`
  `sin_add x y : sin (x + y) = sin x * cos y + cos x * sin y`
  `cos_add x y : cos (x + y) = cos x * cos y - sin x * sin y`
  `sin_sq_add_cos_sq x : (sin x) ^ 2 + (cos x) ^ 2 = 1`
  These can be used as arguments in `rewrite`. For example, if `x` is a real number,
  then `rewrite [sin_sq_add_cos_sq x]` looks for the pattern `(sin x) ^ 2 + (cos x) ^ 2` in the goal
  and replaces it with `1`.

  Can you guess how to type `π`? (Just think LaTeX...)
-/

example (x : ℝ) : sin (x + π) = -sin x := by
  rewrite [sin_add x π]
  rewrite [sin_pi]
  rewrite [cos_pi]
  algebra

example (x : ℝ) : cos (x + π) = -cos x := by
  sorry

-- this one is a bit tricky!
example (x : ℝ) (h : sin x = 0) : (cos x) ^ 2 = 1 := by
  sorry

/-
  Next let's prove a few lemmas. Lemmas are just like examples, but with a name.
  This name allows you to *use* the lemma in other proofs.
-/
lemma cos_sq (x : ℝ) : cos x ^ 2 = 1 - sin x ^ 2 := by
  rewrite [← sin_sq_add_cos_sq x]
  algebra

-- try proving this *using* the lemma `cos_sq`
lemma sin_sq (x : ℝ) : (sin x) ^ 2 = 1 - (cos x) ^ 2 := by
  sorry

lemma twice (x : ℝ) : 2 * x = x + x := by
  sorry


lemma sin_two_mul (x : ℝ) : sin (2 * x) = 2 * sin x * cos x := by
  sorry

lemma cos_two_mul (x : ℝ) : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by
  sorry




/-
  One can leave the arguments in lemma implicit, and for example write
    `rewrite [sin_sq_add_cos_sq]`
  Lean will then search for the pattern `(sin x) ^ 2 + (cos x) ^ 2`, guessing the argument `x`.
  You can also combine several rewrites as follows:
    `rewrite [h1, h2, h3]`
  Try to do the following examples as efficiently as possible
-/

example (x : ℝ) : sin (x + 2 * π) = sin x := by
  sorry

example : sin (x + y + z) = sin x * cos y * cos z + cos x * sin y * cos z +
    cos x * cos y * sin z - sin x * sin y * sin z := by
  sorry



/-
  ## A bit of group theory.

  In principle, Lean can encode all (rigorous) mathematics. Here are a
  few examples from group theory. (There won't be any group theory in the rest of this course.)
-/

variable (G : Type) [Group G]  -- this tells Lean that `G` denotes a group

/-
  The example below proves the following statement: Let `G` be a group and `a` and `b` be
  elements of `G`. Then `(a * a⁻¹) * b = b`.

  The proof uses two lemmas:
    `mul_right_inv a : a * a⁻¹ = 1`
    `one_mul a : 1 * a = a`
    These are in fact axioms of a group. As usual, take a moment to move your
    cursor around in the proof below and see what happens.
-/
example (a b : G) : (a * a⁻¹) * b = b := by
  rewrite [mul_right_inv a]
  rewrite [one_mul b]
  rfl


/-
  The tactic `rfl` proves identities of the form `a = a`.
-/
example (a b : G) : a * (b⁻¹ * b) = a := by
  sorry

/-
  Here is the full list of group axioms.
    `mul_assoc a b c : (a * b) * c = a * (b * c)`
    `mul_right_inv a : a * a⁻¹ = 1`
    `mul_left_inv a : a⁻¹ * a = 1`
    `mul_one a : a * 1 = a`
    `one_mul a : 1 * a = a`

  Now prove the following two examples. Hint: use `\inv` to type `⁻¹`
-/


example (a b : G) : a⁻¹ * (a * b) = b := by
  sorry

example (a b c d : G) : (a * b) * (c * d) = a * (b * (c * d)) := by
  sorry



/-
  Let's do a longer proof. This is the "socks and shoes" law.
-/
example (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- this will reduce the proof to showing that (b⁻¹ * a⁻¹) * (a * b) = 1
  apply inv_eq_of_mul_eq_one_left
  -- now finish the proof yourself
  sorry


/-
  If you need a bigger challenge, try the following exercise. Use the lemma
    `sq a : a ^ 2 = a * a`
  Try to do this as efficiently as possible!
-/

example (a b : G) : a * b ^ 2 * a⁻¹ = (a * b * a⁻¹) ^ 2 := by
  sorry


/-
  Congratulations! You have completed the first worksheet! You have learned to write
  simple Lean proofs using the following tactics:
  - `numbers`, `algebra`, `rfl` for automatically proving simple identities
  - `rewrite` for substituting equalities from hypotheses or Lean lemmas
  Some of this was awkward and cumbersome. Once we learn more tactics, things
  will become much easier...
-/
