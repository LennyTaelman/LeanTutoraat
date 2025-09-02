import Library.Basic

-- todo: wrapper around all lemmas and tactic, with limited scope and helpful
-- doc!

/- # First steps using Lean -/

/-
  You'll work through this file gradually from top to bottom, at your own pace.

  The text written in green (such as these lines here) is for you, it will be ignored by
  Lean.
-/


/-
  ## A first example of a Lean proof

  First we are going to have a look at an example proof, without worrying too
  much about the details.

  Here is what the statement and proof look like in Lean:
-/

example (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  apply le_of_sub_nonneg
  have h : 2 * (a ^ 2 + b ^ 2) - (a + b) ^ 2 = (a - b) ^ 2 := by
    algebra
  rewrite [h]
  apply sq_nonneg

/-
  And here is a line-by-line translation into English.

  Let `a` and `b` be real numbers. Then `(a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2)`. Proof:
    It suffices to show that `0 ≤ 2 * (a ^ 2 + b ^ 2) - (a + b) ^ 2`.
    We claim that `2 * (a ^ 2 + b ^ 2) - (a + b) ^ 2 = (a - b) ^ 2`. Proof:
      This follows from basic algebra.
    Using the claim, we can rewrite the goal as `0 ≤ (a - b) ^ 2`.
    But this is true, because the square of a real number is always non-negative.

  Now move your cursour around in the Lean proof to see what happens in the right panel.

  At any point in the proof, the things before `⊢` tell us what we *have*, and
  the things after `⊢` tell us what we *want*.

  For example, at the start of the proof, before the first `apply`:
    - we *have* that `a` and `b` are real numbers.
    - we *want* to show that `2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2`. This is our *goal*.

  The commands such as `apply`, `have`, `rewrite` are called *tactics*. They are used to
  construct a proof. In the right panel you can keep track of your progress as the proof is being
  built.
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
  sorry

-- Let `a` and `b` be real numbers and assume `a = b`. Then `(a + b) ^ 2 = 4 * a ^ 2`.
example (a b : ℝ) (h : a = b) : (a + b) ^ 2 = 4 * a ^ 2 := by
  sorry


example (a b : ℝ) (h1 : a = 1) (h2 : b = -2) : (a + b) ^ 2 = 1 := by
  sorry

example (x y : ℝ) (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
  sorry


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
  ## Using `rewrite` with a Lean lemma

  In Lean, we write `exp x` for `e ^ x`. (Note that no parenthesis as in
  `exp(x)` are needed.)

  We will prove some statements about the exponential function using the lemma
    `exp_add x y : exp (x + y) = exp x * exp y`
  which is proven in Lean's library.

  The command `rewrite [exp_add a b]` looks for the pattern `exp a + b` in the
  goal and replaces it with `exp a * exp b`.
-/


example (x y : ℝ) (h1 : exp x = 2) : exp (x + y) = 2 * exp y := by
  rewrite [exp_add x y]
  rewrite [h1]
  rfl -- stands for "reflexivity", proves things of the form "a = a".

-- now prove this one yourself
example (x y z : ℝ) : exp ((x + y) + z) = (exp x * exp y) * exp z := by
  sorry

/-
  Let's add the lemmas `exp_zero` and `two_mul` to the mix. We have:
  - `exp_add a b : exp (a + b) = exp a * exp b`
  - `exp_zero : exp 0 = 1`
  - `two_mul a : 2 * a = a + a`
  Prove the following two examples.
-/

example (x : ℝ) : exp (2 * x) = (exp x) ^ 2 := by
  sorry

example (x y : ℝ) (h : x + y = 0) : (exp x) * (exp y) = 1 := by
  sorry


/-
  One can leave the arguments implicit, and just write `rewrite [exp_add]`. Lean
  will then search for the first occurence of the pattern `exp (_ + _)` in the
  goal.

  Tr to do the following example as efficiently as possible
-/

example (x y z t : ℝ) : exp (x + y) * exp (z + t) = exp (x + t) * exp (y + z) := by
  sorry



-- experiment with trigonometric identities

-- tricky: really would love to do some Gröbner stuff, e.g. `algebra [sin_sq_add_cos_sq]`

noncomputable def sin (x : ℝ) : ℝ := Real.sin x
noncomputable def cos (x : ℝ) : ℝ := Real.cos x
def sin_add (x y : ℝ) : sin (x + y) = sin x * cos y + cos x * sin y := Real.sin_add x y

def cos_add (x y : ℝ) : cos (x + y) = cos x * cos y - sin x * sin y := Real.cos_add x y
def sin_zero : sin 0 = 0 := Real.sin_zero
def cos_zero : cos 0 = 1 := Real.cos_zero
def sin_sq_add_cos_sq (x : ℝ) : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

lemma cos_sq (x : ℝ) : cos x ^ 2 = 1 - sin x ^ 2 := by
  rewrite [← sin_sq_add_cos_sq x]
  algebra

lemma sin_sq (x : ℝ) : sin x ^ 2 = 1 - cos x ^ 2 := by
  rewrite [cos_sq x]
  algebra

lemma sin_two_mul (x : ℝ) : sin (2 * x) = 2 * sin x * cos x := by
  rewrite [two_mul x]
  rewrite [sin_add x x]
  algebra

lemma cos_two_mul (x : ℝ) : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by
  rewrite [two_mul x]
  rewrite [cos_add x x]
  algebra

lemma cos_two_mul' (x : ℝ) : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
  rewrite [cos_two_mul]
  rewrite [sin_sq]
  algebra

lemma three_mul (x : ℝ) : 3 * x = (x + x) + x := by
  algebra

example (x : ℝ) : sin (3 * x) = 3 * sin x * cos x ^ 2 - sin x ^ 3 := by
  rewrite [three_mul x]
  rewrite [sin_add]
  rewrite [cos_add]
  rewrite [sin_add]

  algebra


/-
  ## A bit of group theory.

  In theory, Lean can encode anything that is (rigorous) mathematics. Here are a
  few examples from Group Theory. (We won't be doing more group theory in this course.)
-/

-- Let `G` be a group and `a` and `b` be elements of `G`. Then `(a * a⁻¹) * b = b`.
example [Group G] (a b : G) : (a * a⁻¹) * b = b := by
  rewrite [mul_right_inv]
  rewrite [one_mul]
  rfl

-- now do this one yourself, *guess* the names of the lemmas that you need.
example [Group G] (a b : G) : a * (b⁻¹ * b) = a := by
  sorry

/-
  Here is the list of axioms of a group, and Lean's name for them:
    `mul_assoc a b c : (a * b) * c = a * (b * c)`
    `mul_right_inv a : a * a⁻¹ = 1`
    `mul_left_inv a : a⁻¹ * a = 1`
    `mul_one a : a * 1 = a`
    `one_mul a : 1 * a = a`

  Hint: to write `a⁻¹` type `a\inv`

  Now prove the following two examples.
-/


example [Group G] (a b : G) : a⁻¹ * (a * b) = b := by
  sorry

example [Group G] (a b c d : G) : (a * b) * (c * d) = a * (b * (c * d)) := by
  sorry



/-
  Let's do a longer proof. This is the "socks and shoes" law.
-/
example [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- it suffices to show that (b⁻¹ * a⁻¹) * (a * b) = 1
  apply inv_eq_of_mul_eq_one_left
  -- now finish the proof with a series of rewrites
  sorry


/-
  If you need a bigger challenge, try the following exercise. Use the lemma
    `sq a : a ^ 2 = a * a`
-/

example [Group G] (a b : G) : a * b ^ 2 * a⁻¹ = (a * b * a⁻¹) ^ 2 := by
  sorry
