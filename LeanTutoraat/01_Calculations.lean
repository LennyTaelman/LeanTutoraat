import Library.Basic
tutoraat_init



/- # Exercise sheet 1: Proving equalities and inequalities -/

/- ## Recap: numerical identities with `numbers`  -/

/-

  The tactic `numbers` proves equalities and inequalities
  between "numerical" expressions  without variables. We've
  already seen the "equalities" part in the introductory sheet.
-/

example : 1 + 1 = 2 := by
  numbers

example : 2 > 1 := by
  numbers

/-
  The tactic `sorry` is used to skip a proof. ("Sorry, I'll do this later!").
  In the four examples below, replace `sorry` with `numbers`, and see what happens.
-/

example : 2 ^ 7 ≥ 5 ^ 3 := by
  sorry

example : (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9) ^ 2 = 2025 := by
  sorry

example : 1 + 1 = 3 := by
  sorry

example (a : ℝ) : a + 1 > a := by
  sorry


/- ## Recap: algebraic identities using `algebra` -/

/-
  In the following example, the expression `(a : ℝ)` before the `:` means that
  `a` denotes an (arbitrary) real number. So the example states that for all real
  numbers `a` the identity `(a + 1) * (a - 1) = a ^ 2 - 1` holds.
-/
example (a : ℝ) : (a + 1) * (a - 1) = a ^ 2 - 1 := by
  algebra

example (a b : ℤ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  algebra

/-
  In the four examples below, replace `sorry` with `algebra`, and see what happens.
-/

example (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  sorry

example (a b : ℚ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry

example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  sorry

example (a : ℝ) : a ^ 2 ≥ 0 := by
  sorry


/-
  Now state and prove the theorem that for all real numbers `a`, `b`, `c`
  the identity `a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a)`
  holds.

  To write the symbol ℝ, use `\R` or `\real`.
-/





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
  Let's add one more variant
    `rewrite [h1] at h2` substites `h1` into the hypothesis `h2` (and not the goal)
-/

-- TODO add example for `rewrite [h1] at h2`

example (a b : ℝ) (ha : a = 1) (hb : b = 0) : (a + b) ^ 8 = 1 := by
  sorry

example (a b c : ℝ) (ha : c = a) (hb : b = -c) : a + b = 0 := by
  sorry

example (x y : ℝ) (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
  sorry

example (a b c d : ℤ) (h1 : c = a + b) (h2 : d = b - a) : c * d = b ^ 2 - a ^ 2 := by
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
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by numbers

-- Replace each `sorry` with a valid justification.
example (r s : ℝ) (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = (r + 2 * s) - 2 * s := by sorry
    _ = -1 - 2 * s := by sorry
    _ = -1 - 2 * 3 := by sorry
    _ = -7 := by sorry

-- Replace each `sorry` with a valid justification.
example (x y z : ℤ) (h1 : x + y + z = 0) (h2 : x * y + y * z + z * x = 0) :
  x ^ 2 + y ^ 2 + z ^ 2 = 0 := by
  calc
    x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by sorry
    _ = 0 ^ 2 - 2 * 0 := by sorry
    _ = 0 := by sorry


/-
  Now it is time to write your own `calc` proofs. The syntax can be a bit
  finnicky at first, but it gets easier with practice. I recommend you first
  write the `calc` block with `sorry`'s, and then fill in the justifications.
  ```
  calc
    LHS = ... := by sorry
    _ = ... := by sorry
    _ = ... := by sorry
    _ = RHS := by sorry
  ```
  where `h1`, `h2`, `h3` are hypotheses or lemmas.
-/

/-
  Replace `sorry` with a correct `calc` proof. Hint:
  `(b - a) ^ 2 = (a + b) ^ 2 - 4 * (a * b) = s ^ 2 - 4 * t`
-/
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

  TODO: consider eliminating `positivity`, as it is subsumed by `extra`.
-/

example (a : ℝ) (h : a > 1) : a > 0 := by
  positivity

example (a b : ℝ) (h1 : a > 0) (h2 : b > 0) : a * b > 0 := by
  positivity

example (a : ℝ) : a + 2 > a := by
  extra

example (a b : ℤ) (h : a ≥ 0) : a + b ≥ b := by
  extra

-- check that `extra` cannot prove the following (why?)
example (a b : ℝ) : a + b ≥ b := by
  sorry

-- check that `extra` *can* prove the following (why?)
example (a b : ℕ) : a + b ≥ b := by
  sorry


/-
  In the following examples, replace `sorry` by either `positivity` or `extra`.
-/


example (a : ℝ) (b : ℝ) : a + b ^ 2 ≥ a := by
  sorry

example (a : ℝ) : a - 1 < a := by
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
-/


example (a b : ℝ) : a ^ 2 + b ^ 2 - 2 * a * b ≥ 0 := by
  calc
    a ^ 2 + b ^ 2 - 2 * a * b = (a - b) ^ 2 := by sorry
    _ ≥ 0 := by sorry

-- Note: in the above proof, the result of chaining a `=` and a `≥` is a `≥`

/-
  Now write your own `calc` proof for the following inequality.
  Hint: type `≤` using `\le` (less than or equal) and `≥` using `\ge` (greater than or equal).
-/
example (a : ℝ) : a + 2 ≥ a + 1 := by
  sorry

-- Note that `extra` cannot directly prove this (why?). Give a proof using `calc`.
example (a b c : ℝ) : (c + a ^ 2) + 1 > c := by
  sorry




/- ## Substituting inequalities with `rel` -/

/-
  The tactic `rel` is somewhat similar to `rw`, but is used to prove
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
  Warning: in the example below, the tactic `rel [h1]` *sees* the hypothesis h : a > 0, which is
  *needed* to deduce that a * b > a * c.
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
    _ = 2 * (x ^ 2 + y ^ 2) := by sorry
    _ ≤ 2 * 1 := by sorry
    _ = 2 := by sorry


/-
  Replace `sorry` with a correct `calc` proof. Hint, one proof uses the chain:
  `n * n ≥ 5 * n = 2 * n + 3 * n ≥ 2 * n + 15`
  but you might need to provide more intermediate steps...
-/
example (n : ℤ) (h : n ≥ 5) : n ^ 2 > 2 * n + 11 := by
  sorry




/-
  Congratulations! You have completeed the first worksheet. You
  have learned to write proofs using the following tactics:

  - `numbers` and `algebra` for automatically proving simple identities
  - `rw` for substituting equalities
  - `calc` for chaining together equalities and/or inequalities
  - `extra` and `positivity` for automatically proving simple inequalities
  - `rel` for substituting inequalities
-/



/- ## THINGS TO INTEGRATE SOMEWHERE -/



-- various things related to division/multiplication and inequalities

example (a b : ℝ) (h1 : a > 0) (h2 : b > 0) : a / b > 0 := by positivity

-- hint: use that a = c / b
example (a b : ℝ) (h1 : a * b = c) (h2 : b > 0) (h3 : c > 0) : a > 0 := by
  calc
    a = (a * b) / b := by algebra
    _ = c / b := by rw [h1]
    _ > 0 := by positivity

example (a : ℝ) (h : a > 1) : 1 / a < 1 := by
  calc
    1 / a = 1 * (1 / a) := by ring
    _ < a * (1 / a) := by rel [h]
    _ = 1 := by field_simp

example (a b : ℝ) (h1 : a * b = 1) (h2 : a ≥ 1) : b ≤ 1 := by
  -- tricky: we don't have b>0 yet, so cannot say b ≤ a * b
  have h : a * b ≤ a * 1 := by
    calc
      a * b = 1  := by rw [h1]
      _ ≤ a := by rel [h2]
      _ = a * 1 := by ring
  cancel a at h


-- things with division

-- this is horrible now; what is the proper idomatic way to do this?
example (a b : ℝ) (h1 : a > 0) (h2 : b > 1) : a / b < a := by
  have h : a / b > 0 := by positivity
  calc
    a / b = (a / b) * 1 := by ring
    _ < (a / b) * b := by rel [h2]
    _ = a := by field_simp

example (a b : ℝ) (h2 : b ≠ 0) : b * a / b = a := by field_simp; ring


-- first attempts at  using simp/field_simp

example (a : ℝ) (b : ℝ) (h : a = 1) : a - 1 = 0  * b := by
  -- simp
  rw [h]
  simp

example (a b c : ℝ) (h : c ≠ 0) : a / (1 / c) + b = a * c + b := by
  field_simp


-- more division "identities"

-- note that field_simp does not work if you comment out the h1 or h2
-- since cannot cancel a or b unless we know they are nonzero
lemma test (a b : ℝ) (h : a * b = 1) : 1 / a + 1 / b = a + b := by
  have h1 : a ≠ 0 := by exact left_ne_zero_of_mul_eq_one h
  have h2 : b ≠ 0 := by exact right_ne_zero_of_mul_eq_one h
  calc
    1 / a + 1 / b = (a * b) / a + (a * b) / b := by rw [h]
    _ = a + b := by field_simp; ring


-- a simple but surprisingly tricky inequality

example (a b : ℝ) (h : a ≤ b) : 0 ≤ b - a := by
  calc
    0 ≤ a - a := by algebra
    _ ≤ b - a := by rel [h]
