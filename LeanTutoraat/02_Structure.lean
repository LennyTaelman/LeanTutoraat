/- Copyright (c) Lenny Taelman, 2025.  All rights reserved. -/
import Library.Basic
tutoraat_init


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

/-! # Extra challenges -/
