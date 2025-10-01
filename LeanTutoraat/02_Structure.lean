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
-/

lemma sub_nonneg_of_ge (x y : ℝ) (h : y ≥ x) : 0 ≤ y - x := by
  sorry

example (x y a b : ℝ) (h1 : x ≤ y) (h2 : a ≤ b) : a * y + b * x ≤ a * x + b * y := by
  have h1' : 0 ≤ y - x := by apply sub_nonneg_of_ge x y h1
  have h2' : 0 ≤ b - a := by apply sub_nonneg_of_ge a b h2
  calc
    a * y + b * x ≤ (a * y + b * x) + (b - a) * (y - x) := by extra
                _ = a * x + b * y                       := by algebra




-- and we can re-use the lemma in other proofs:

-- TODO: example!










example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring
  cancel 2 at h3


example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  sorry

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  sorry

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  sorry

/-! # Exercises -/




example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  sorry

example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  sorry


/-! ## Invoking a lemma with `apply` -/


/-! ## Proving ∀-statements with `intro` -/


/-! ## Proving ∃-statements with `use` -/
