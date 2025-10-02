import Library.Basic
tutoraat_init



/- # Exercise sheet 1: Proving equalities and inequalities -/

/- ## Recap: using `rfl`,`numbers` and `algebra`  -/

/-
  Last week we've seen three basic tactics to prove `trivial' equalities:
    `rfl` proves identities of the form `a = a`
    `numbers` proves identities between numerical expressions without variables
    `algebra` proves algebraic identities
   In fact, `rfl` and `numbers` can also prove inequalities, see
   the examples below.

   Use `\ge` and `\le` to type `≥` and `≤`. (Read: "greater/less than or equal to")
-/

example : 2 ≥ 2 := by
  rfl

example : 5 ^ 2 < 2 ^ 7 := by
  numbers

/-
  Let's practice a bit before moving on with new material. Replace `sorry` with
  a correct proof in the following examples. Try to use the lightest tactic that
  does the job (`rfl` being the lightest, and `algebra` the heaviest).
-/


example : 7 * 11 * 13 > 1000 := by
  sorry

example : 0 ≤ 0 := by
  sorry

example (a b : ℤ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

example : (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9) ^ 2 = 2025 := by
  sorry

example (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  sorry

example (x y : ℝ) : x + y ≥ x + y := by
  sorry



/- ## Recap: substituting with `rewrite` -/

/-
  In the following example, `h` is the hypothesis that `a = 2`.
  To prove that `a ^ 2 = 4` we use the `rewrite` tactic
  to substitute `a` with `2` in the goal.
-/

example (a : ℚ) (h : a = 2) : a ^ 2 = 4 := by
  rewrite [h] -- this uses hypothesis h to substitute a with 2
  numbers

/-
  Last session, we've seen a few variants of this usage.
    `rewrite [h]` where `h : a = b`  substitutes `a` with `b` in the goal.
    `rewrite [←h]` where `h : a = b` substitutes `b` with `a` in the goal.
    `rewrite [h1, h2]` first substitues using `h1`, then using `h2`
  Let's add one more variant:
    `rewrite [h1] at h2` substites `h1` into the hypothesis `h2` (and not the goal)

  Now replace the `sorry` below with correct proofs.
-/


example (a b : ℝ) (h : a + b = 2) : (a + b) ^ 4 = 16 := by
  sorry

example (a b c : ℝ) (h1 : c = a) (h2 : b = -c) : a + b = 0 := by
  sorry

example (a b n : ℕ) (h1 : n = a * b) (h2 : a = 2) (h3 : b = 3) : n = 6 := by
  sorry

example (x y : ℝ) (h1 : x = 3) (h2 : 4 * x - 3 = y) : y = 9 := by
  sorry

example (a b c d : ℤ) (h1 : a + b = c) (h2 : b - a = d) : c * d = b ^ 2 - a ^ 2 := by
  sorry



/- ## Chaining equalities together with `calc` -/

/-
  The `calc` tactic can be used to prove an equality of the form
  `LHS = RHS` by proving `LHS = ... = ... = ... = RHS`.
  Each individual equality must be justified with its own proof.

  The following example shows how to use it to prove that `(a + b) ^ 2 = 20`
  given that `a - b = 4` and `a * b = 1`. The proof boils down to the chain
  of equalities
  `(a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) = 4 ^ 2 + 4 * 1 = 20`.
-/

example (a b : ℚ) (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by algebra
              _ = 4 ^ 2 + 4 * 1             := by rewrite [h1, h2]; rfl
              _ = 20                        := by numbers


-- Replace each `sorry` with a valid justification.
example (r s : ℝ) (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 := by
  calc
    r = (r + 2 * s) - 2 * s := by sorry
    _ = -1 - 2 * s          := by sorry
    _ = -1 - 2 * 3          := by sorry
    _ = -7                  := by sorry

-- Replace each `sorry` with a valid justification.
example (x y : ℤ) (h1 : x + y = 2) (h2 : x * y = 1) : x ^ 3 + y ^ 3 = 2 := by
  calc
    x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by sorry
                _ = 2 ^ 3 - 3 * 1 * 2                   := by sorry
                _ = 2                                   := by sorry

/-
  Now it is time to write your own `calc` proofs. The syntax can be a bit
  finnicky at first, but it gets easier with practice. I recommend you first
  write the sequence of equalities on a sheet of paper. Then create a `calc`
  block where each step is justified by a `sorry`. Then fill in the justifications.
-/

-- Replace `sorry` with a correct `calc` proof.
example (a b : ℝ) (h1 : a + b = s) (h2 : a * b = t) : (b - a) ^ 2 = s ^ 2 - 4 * t := by
  sorry

-- Replace `sorry` with a correct `calc` proof
example (a b : ℤ) (h : a - b = 0) : a = b := by
  sorry

-- Replace `sorry` with a correct `calc` proof
example (x y : ℤ) (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 := by
  sorry

-- Replace `sorry` with a correct `calc` proof
example (p q : ℚ) (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 := by
  sorry



/- ## Simple inequalities with `extra` and `positivity` -/

/-
  The tactic `positivity` tries to automatically prove goals of the form
  `a > 0` or `a ≥ 0`.

  The tactic `extra` proves inequalities of the form `a + e > a`
  or `a + e ≥ a`. It detects the "extra" term `e` that is added
  and tries to automatically prove that `e > 0` or `e ≥ 0`.
-/

example (a : ℝ) (h : a > 1) : a > 0 := by
  positivity

example (a b : ℝ) (h1 : a > 0) (h2 : b > 0) : a * b > 0 := by
  positivity



example (a : ℝ) : a + 2 > a := by
  extra

example (a b : ℤ) (h : a ≥ 0) : a + b ≥ b := by
  extra


/-
  In the following examples, replace `sorry` by either `positivity` or `extra`.
  Try to use the lighter tactic (being `positivity`) when possible.
  Exactly one of these statements is *false*. Can you tell which one before trying?
-/


example (a : ℝ) (b : ℝ) : a + b ^ 2 ≥ a := by
  sorry

example (a : ℝ) : a - 1 < a := by
  sorry

example (a b : ℕ) : a + b ≥ b := by
  sorry

example (a b : ℝ) : a + b ≥ a := by
  sorry

example (a b : ℝ) (h1 : a > 0) (h2 : b > 0) : a / b > 0 := by
  sorry

example (a : ℝ) : a ^ 2 ≥ 0 := by
  sorry

example (a b : ℚ) (h1 : a ≥ 0) (h2 : b ≥ 0) : a * b + 1 > 0 := by
  sorry

example (a b : ℝ) (h : e ≥ 0) : a - e ≤ a := by
  sorry

example (a b c : ℝ) : c + (a ^ 2 + 1) > c := by
  sorry

example (a b : ℝ) (h1 : a > 0) (h2 : b ≥ 0) : a * b ≥ 0 := by
  sorry


/-
  Inequalities and equalities can be chained together using `calc` again. Fill
  in the justifications for both steps in the proof below.

  Note: we prove `≥` by chaining a `=` and a `≥` in this proof.
-/


example (a b : ℝ) : a ^ 2 + b ^ 2 - 2 * a * b ≥ 0 := by
  calc
    a ^ 2 + b ^ 2 - 2 * a * b = (a - b) ^ 2 := by sorry
                            _ ≥ 0           := by sorry


/-
  Now write your own `calc` proof for the following inequality.
-/
example (a : ℝ) : a + 2 ≥ a + 1 := by
  sorry

-- Note that `extra` cannot directly prove this (why?). Give a proof using `calc`.
example (a b c : ℝ) : (c + a ^ 2) + 1 > c := by
  sorry




/- ## Substituting inequalities with `rel` -/

/-
  The tactic `rel` is somewhat similar to `rewrite`, but is used to prove
  inequalities.
-/


example (a : ℝ) (h : a ≥ b) : a + 1 ≥ b + 1 := by
  rel [h]

example (a b c : ℝ) (h : a > b) : a + c > b + c := by
  rel [h]

example (a b c : ℝ) (h : a > b) : c - a < c - b := by
  rel [h]

example (a b : ℝ) (h : a ≥ b) : 3 * a ≥ 3 * b := by
  rel [h]

/-
  Warning: in the example below, the tactic `rel [h1]` *sees* the hypothesis `h2 : c > 0`, which
  is *needed* to deduce that a * b > a * c.
-/
example (a b c : ℝ) (h1 : a > b) (h2 : c > 0) : a * c > b * c := by
  rel [h1]

-- indeed: check that `rel` does not prove the following (false) claim
example (a b c : ℝ) (h1 : a > b) :  a * c > b * c := by
  sorry -- FALSE



-- Justify each step in the proof below.
example (x y : ℝ) (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 ≤ 2 := by
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by sorry
              _ = 2 * (x ^ 2 + y ^ 2)       := by sorry
              _ ≤ 2 * 1                     := by sorry
              _ = 2                         := by sorry


/-
  Replace `sorry` with a correct `calc` proof. Hint, one proof uses the chain:
  `n * n ≥ 5 * n = 2 * n + 3 * n ≥ 2 * n + 15`
  but you might need to provide more intermediate steps...
-/
example (n : ℤ) (h : n ≥ 5) : n ^ 2 > 2 * n + 11 := by
  sorry

-- Replace `sorry` with a correct `calc` proof.
example (a b : ℝ) (h : a ≤ b) : 0 ≤ b - a := by
  sorry

-- Replace `sorry` with a correct `calc` proof. This one is tricky...
example (a : ℝ) (h : a > 1) : 1 / a < 1 := by
  sorry

-- Replace `sorry` with a correct `calc` proof.
example (a b c : ℝ) (h1 : a * b = c) (h2 : b > 0) (h3 : c > 0) : a > 0 := by
  sorry


/-
  Congratulations! You have completeed the first worksheet. You
  have learned to write proofs using the following tactics:

  - `rfl`, `numbers` and `algebra` for automatically proving simple identities
  - `rewrite` for substituting equalities
  - `calc` for chaining together equalities and/or inequalities
  - `extra` and `positivity` for automatically proving simple inequalities
  - `rel` for substituting inequalities
-/
