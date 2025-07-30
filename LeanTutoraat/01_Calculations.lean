/- Copyright (c) Lenny Taelman, 2025. Based on "Mechanics of Proof" by Heather Macbeth. -/

import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init




/- # Exercise sheet 1: Proving equalities and inequalities -/

/- ## Purely numerical statements using `numbers` -/


/-
  The tactic `numbers` proves equalities between "numerical" expressions
  not involving any variables
-/
example : 1 + 1 = 2 := by
  numbers

-- `numbers` can also prove inequalities
example : 5 + 1 > 5 := by
  numbers

-- replace the word `sorry` with the correct justification
example : 2 ^ 7 > 5 ^ 3 := by
  sorry

-- replace the word `sorry` with the correct justification
example : (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9) ^ 2 = 2025 := by
  sorry

-- see what happens when you try to prove a statement that is false
example : 1 + 1 = 3 := by
  sorry




/- ## Identities involving addition and multiplication with `ring` -/

/-
  In the following example, the expression `(a : ℝ)` before the `:` means that
  `a` denotes an (arbitrary) real number. So the example states that for all real
  numbers `a` the identity `(a + 1) * (a - 1) = a ^ 2 - 1` holds.

  The `ring` tactic can prove this.
-/
example (a : ℝ) : (a + 1) * (a - 1) = a ^ 2 - 1 := by
  ring

example (a b : ℤ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  ring

-- Replace the word `sorry` with the correct Lean justification.
example (a b : ℚ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry

-- Replace the word `sorry` with the correct Lean justification.
example (a b : ℝ) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  sorry

-- Check that `ring` does *not* work here (why?)
example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  sorry

-- This is true, but `ring` cannot prove it. We'll learn how to prove it later.
example (a : ℝ) : a ^ 2 ≥ 0 := by
  sorry


/-
  Now state and prove the theorem that for all real numbers `a`, `b`, `c`
  the identity `a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a)`
  holds.

  To write the symbol ℝ, use `\R` or `\real`.
-/



/- ## Substituting with `rw` -/

/-
  In the following example, `h` is the hypothesis that `a = 2`.
  To prove that `a ^ 2 = 4` we use the `rw` tactic (for *rewrite*)
  to substitute `a` with `2` in the goal.

  Note that we've already used the `rw` tactic in the introductory session.
-/

example (a : ℚ) (h : a = 2) : a ^ 2 = 4 := by
  rw [h] -- this uses hypothesis h to substitute a with 2
  numbers

example (a b : ℝ) (h : a = b) : (a + b) ^ 2 = 4 * a ^ 2 := by
  rw [h]
  ring

-- One can also use `rw` to do multiple substitutions in one go.
example {a b : ℝ} (ha : a = 1) (hb : b = 0) : (a + b) ^ 8 = 1 := by
  rw [ha,hb]
  numbers

-- replace `sorry` with a correct proof
example (x y : ℝ) (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
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

-- Replace the words "sorry" with the correct Lean justification.
example (r s : ℝ) (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = (r + 2 * s) - 2 * s := by sorry
    _ = -1 - 2 * s := by sorry
    _ = -1 - 2 * 3 := by sorry
    _ = -7 := by sorry

-- Replace the words "sorry" with the correct Lean justification.
example (x y z : ℤ) (h1 : x + y + z = 0) (h2 : x * y + y * z + z * x = 0) :
  x ^ 2 + y ^ 2 + z ^ 2 = 0 := by
  calc
    x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by sorry
    _ = 0 ^ 2 - 2 * 0 := by sorry
    _ = 0 := by sorry


/-
  Now it is time to write your own `calc` proofs. The syntax can be a bit
  finnicky at first, but it gets easier with practice.

  Here is an example of a "chain" proof.

  hypothesis: `a + b = s` and `a * b = t`
  claim: `(b - a) ^ 2 = s ^ 2 - 4 * t`

  proof by calculation:
  `(b - a) ^ 2 = (a + b) ^ 2 - 4 * (a * b) = s ^ 2 - 4 * t`
-/
example (a b : ℝ) (h1 : a + b = s) (h2 : a * b = t) : (b - a) ^ 2 = s ^ 2 - 4 * t := by
  sorry

-- Replace `sorry` with a correct proof
example {a b : ℤ} (h : a - b = 0) : a = b :=
  sorry

-- Replace `sorry` with a correct proof
example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  sorry

-- Replace `sorry` with a correct proof
example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  sorry



/-! ## Proving inequalities with `rel` -/

example {a : ℝ} (h : a ≥ b) : a + 1 ≥ b + 1 := by
  rel [h]

example {a b : ℝ} (h : a > b) : a + 1 ≥ b + 1 := by
  rel [h]

-- CAREFUL: "rel [h2]" here *sees* the hypothesis h : a > 0, which is
-- NEEDED to deduce that a * b > a * c.
example {a b : ℝ} (h : a > 0) (h2 : b > c) : a * b > a * c := by
  rel [h2]

-- indeed: check that the following does not work:
example {a b : ℝ} (h2 : b > c) : a * b > a * c := by
  sorry


-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers

-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  calc
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by addarith [h1, h2]
    _ = 3 := by ring

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  sorry


-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by sorry
    _ ≥ 10 * t - 3 * t - 17 := by sorry
    _ = 7 * t - 17 := by sorry
    _ ≥ 7 * 10 - 17 := by sorry
    _ ≥ 5 := by sorry

-- Example 1.4.6
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  sorry



-- Example 1.4.8
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by sorry
    _ = 2 * (x ^ 2 + y ^ 2) := by sorry
    _ ≤ 2 * 1 := by sorry
    _ < 3 := by sorry



example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  sorry

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  sorry

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  sorry

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  sorry


/-! ## Proving inequalities with `addarith` -/


example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  addarith [h1]


example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 := by
  addarith [h]
