/- Copyright (c) Lenny Taelman, 2025.  All rights reserved. -/
import Library.Basic


/-! # Proofs with structure -/


/-! ## Establishing intermediate results with `have` -/


/-
  If `b ≥ a` and `c ≥ 0`, then `(b - a) * c ≥ 0`. This looks like something that
  `positivity` can prove, but `positivity` won't be able to see that
  `b - a ≥ 0`. One way to deal with this is to make a side-step, and first
  establish the result that `b - a ≥ 0`.

  As usual: take some time to move the cursor around in the proof and see what
  happens. Note:
  - the proof of `h3` is indented (moved 2 spaces to the right)
  - if you place the cursor right before `positivity` you'll see that `h3` has
    been added to the list of things we have, so `positivity` will be able to
    use it.
-/
example (a b c d : ℝ) (h1 : b ≥ a) (h2 : c ≥ 0) : (b - a) * c ≥ 0 := by
  have h3 : b - a ≥ 0 := by
    calc
      0 = a - a := by algebra
      _ ≤ b - a := by rel [h1]
  positivity



-- here is a longer example. Replace each `sorry` with a correct proof.
example (r s : ℚ) (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by
    sorry
  have h4 : r ≤ 3 - s := by
    sorry
  calc
    r = (r + r) / 2           := by sorry
    _ ≤ (3 - s + (3 + s)) / 2 := by sorry
    _ = 3                     := by sorry


/-
  In the proof below, `h3` is used in order to avoid division by zero. Fill
  in the proof of `h3`.
-/
example (a b : ℝ) (h1 : a * b = 0) (h2 : a - 1 > 0) : b = 0 := by
  have h3 : a > 0 := by
    sorry
  calc
    b = a * b / a := by algebra
    _ = 0 / a := by rewrite [h1]; rfl
    _ = 0 := by algebra


/-
  Here is a longer example. If `x ^ 2 = 4` then either `x = 2` or `x = -2`. So
  if we also know that `1 < x`, then we must have `x = 2`. Replace each `sorry`
  with a correct justification.
-/
example (x : ℚ) (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  -- first rewrite `h1` in a more useful form
  have h3 : (x - 2) * (x + 2) = 0 := by
    sorry
  -- now use `h2` to show that `x + 2 > 0`
  have h4 : 0 < x + 2 := by
    sorry
  -- hint for `h5`: have a look at the previous example
  have h5 : x - 2 = 0 := by
    sorry
  -- finally, deduce that `x = 2` to finish the proof.
  sorry

/-
  TODO: example where student needs to formulate the `have` statement.
-/


/-! ## Invoking lemmas with `apply` -/

/-! ## Outsourcing intermediate results to lemmas -/

/-
  The inequality below is called the "rearrangement inequality". It abstracts
  the following intuitively obvious fact: if `b > a`, and you need to
  choose between either
  - picking `b` valuable and `a` worthless items, or
  - picking `a` valuable and `b` worthless items,
  then the first option is clearly better.

  The proof boils down to the chain
    `a * y + b * x ≤ (a * y + b * x) + (b - a) * (y - x) = a * x + b * y`
  where we used that `b - a ≥ 0` and `y - x ≥ 0`. Here is one way to write the proof:
-/


example (x y a b : ℝ) (h1 : x ≤ y) (h2 : a ≤ b) : a * y + b * x ≤ a * x + b * y := by
  -- we first show that y - x ≥ 0
  have h1' : y - x ≥ 0 := by
    calc
      0 ≤ x - x := by algebra
      _ ≤ y - x := by rel [h1]
  -- similarly, b - a ≥ 0
  have h2' : b - a ≥ 0 := by
    calc
      0 ≤ a - a := by algebra
      _ ≤ b - a := by rel [h2]
  -- now `extra` will be able to deduce that (b - a) * (y - x) ≥ 0
  calc
    a * y + b * x ≤ (a * y + b * x) + (b - a) * (y - x) := by extra
                _ = a * x + b * y                       := by algebra

/-
  This looks inefficient! We are doing the same proof twice. We should extract the
  repeated part into a lemma. Replace the `sorry` below with a correct proof.

  Note that the statement of a `lemma` is the same as that of an `example`, but
  that it requires a name (so we can refer to it). Do you understand the choice
  of name?
-/

lemma sub_nonneg_of_ge (x y : ℝ) (h : x ≤ y) : 0 ≤ y - x := by
  sorry

-- now the proof is much shorter
example (x y a b : ℝ) (h1 : x ≤ y) (h2 : a ≤ b) : a * y + b * x ≤ a * x + b * y := by
  have h1' : 0 ≤ y - x := by
    apply sub_nonneg_of_ge x y h1
  have h2' : 0 ≤ b - a := by
    apply sub_nonneg_of_ge a b h2
  calc
    a * y + b * x ≤ (a * y + b * x) + (b - a) * (y - x) := by extra
                _ = a * x + b * y                       := by algebra

/-
  Note that the lemma takes three arguments: two real numbers and the fact that
  the first is less than the second.

  We can now re-use the lemma in other proofs:
-/



example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h1' : 0 ≤ a - (-b) := by
    sorry
  have h2' : 0 ≤ b - a := by
    sorry
  calc
    a ^ 2 ≤ a ^ 2 + (b - a) * (a - (-b)) := by sorry
        _ = b ^ 2                        := by sorry



/-
  Now let's do a more involved example.
  1) first prove the first inequality (hint: "complete the square")
  2) then turn it into a lemma (and in particular give it a name)
  3) finally use the lemma to prove the second inequality
-/

example (a b : ℝ) : a ^ 2 + a * b + b ^ 2 ≥ 0 := by
  sorry

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  sorry




/-! ## Proving ∀-statements with `intro` and ∃-statements with `use` -/

/-
  To prove a statement of the form "∀ `x` in `ℝ`, it holds that....", one typicall starts with
  "Let `x` be a real number" and then reasons that the things holds for this
  (arbitrarily chosen) `x`.

  In Lean, this is achieved with the `intro` tactic. Examine the proof below by
  moving the cursor around.
-/

example : ∀ x : ℝ, x ^ 2 ≥ 0 := by
  intro x
  positivity


/-
  To prove a statement of the form "∃ `n` in `ℝ` such that ...", one typically
  starts with "Take `n` to be such and such. We now show that it satisfies the
  desired property."

  In Lean, this is achieved with the `use` tactic. Examine the proof below by
  moving the cursor around.
-/

example : ∃ n : ℤ, 81 * n = 2025 := by
  use 25
  numbers


/-
  Now do the following exercises.
-/

example : ∀ x : ℕ, ∃ y : ℕ, x < y := by
  sorry

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  sorry

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  sorry

example (x : ℝ) : ∃ y : ℝ, x ≤ y ^ 2 := by
  sorry

example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  sorry



/-! # `linarith` to automate systems of linear equalities and inequalities -/

/-
  Many of the proofs we have seen so far can be automated. The tactic
  `linarith` automatically proves linear inequalities of equalities
  from hypotheses which are linear equalities or inequalities.
-/

example (x y : ℝ) (h1 : x + 1 = 0) (h2 : x + y = 1): y = 2 := by
  linarith

example (a b : ℝ) (h1 : a > 2) (h2 : a + b < 3) : b < 1 := by
  linarith

example (n : ℕ) : n + 1 ≥ 1 := by
  linarith

/-
  Below are many examples that we have seen earlier, and can now be
  solved much more easily. Some of these involved rather long `calc` proofs.

  This is a general principle in Lean: tasks for which there is an obvious
  procedure (e.g. Gauss elimination for solving linear systems) should be
  automated.

  Prove the following 10 examples. Try to do them in *one attempt*: Convince
  yourself of the correct Lean proof before trying...

  Hint: all of them can be proven using just one line. For most of them
  `linarith` will work, but not for all...
-/

example (x y : ℝ) (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
  sorry

example (r s : ℝ) (h1 : s = 3) (h2 : r + 2 * s > -1) : r > -7 := by
  sorry

example (a b : ℤ) (h : a - b = 0) : a = b := by
  sorry

example (n m : ℕ) : n + m ≥ m := by
  sorry

example (p q : ℚ) (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 := by
  sorry

example (a b c : ℝ) (h1 : a > b) (h2 : c > 0) : a * c > b * c := by
  sorry

example (a b : ℤ) (h : a ≥ 0) : a + b ≥ b := by
  sorry

example (a b c : ℝ) : a - c ^ 2 ≤ a := by
  sorry

example (a b c : ℝ) (h : a > b) : c - a < c - b := by
  sorry

example (a b : ℝ) (h : a ≥ b) : 3 * a ≥ 3 * b := by
  sorry

/-
  How many did you manage to do at the first attempt?
-/


/-
  Even in things that are not entirely linear, `linarith` can be very useful.
  Here is an example:
-/

example (x y : ℝ) (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 ≤ 2 := by
  have h1 : (x - y) ^ 2 ≥ 0 := by positivity
  have h2 : (x + y) ^ 2 + (x - y) ^ 2 = 2 * (x ^ 2 + y ^ 2) := by algebra
  -- now our goal is a linear combination of `h`, `h1` and `h2` so `linarith` can handle it.
  linarith

/-
  This one we did above before knowing `linarith`. Now do it again, using
  `linarith` generously!
-/

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h1' : 0 ≤ b + a := by sorry
  have h2' : 0 ≤ b - a := by sorry
  have h3 : b ^ 2 - a ^ 2 ≥ 0 := by sorry
  sorry

/-
  Finally, a more challenging example! Hint: work out the argument on paper first!
-/

example (x y z c : ℝ) (h : x + y + z = c) : ∃ d : ℝ, x * y + y * z + z * x ≤ d := by
  sorry
