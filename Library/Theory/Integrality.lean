import Mathlib.Data.Real.Basic

/-!
# Integrality and Rationality

This file defines what it means for a real number to be an integer or rational,
and proves basic properties of these notions.

## Main definitions

* `isInt x` - states that the real number `x` is an integer
* `isRat x` - states that the real number `x` is rational

## Main lemmas

For `isInt`, we provide lemmas showing:
- Basic numbers like 0, 1, and coercions from ℕ and ℤ are integers
- Integers are closed under addition, subtraction, and multiplication

For `isRat`, we provide lemmas showing:
- Basic numbers like 0, 1, and coercions from ℕ and ℤ are rational
- Inverses of natural numbers are rational
- Rationals are closed under addition, subtraction, and multiplication
-/

/-- A real number `x` is an integer if there exists an integer `N` such that `x = N`. -/
def isInt (x : ℝ) : Prop := ∃ N : ℤ, x = N

/-- The real number `0` is an integer. -/
lemma isInt_zero : isInt 0 := by use 0; norm_cast

/-- The real number `1` is an integer. -/
lemma isInt_one : isInt 1 := by use 1; norm_cast

/-- Every natural number is an integer (when viewed as a real number). -/
lemma isInt_nat (n : ℕ) : isInt (n : ℝ) := by use n; rfl

/-- Every integer is an integer (when viewed as a real number). -/
lemma isInt_int (n : ℤ) : isInt (n : ℝ) := by use n

/-- The sum of two integers is an integer. -/
lemma isInt_add {x y : ℝ} (hx : isInt x) (hy : isInt y) : isInt (x + y) := by
  obtain ⟨N, hN⟩ := hx
  obtain ⟨M, hM⟩ := hy
  use N + M
  rw [hN, hM]
  norm_cast

/-- The difference of two integers is an integer. -/
lemma isInt_sub {x y : ℝ} (hx : isInt x) (hy : isInt y) : isInt (x - y) := by
  obtain ⟨N, hN⟩ := hx
  obtain ⟨M, hM⟩ := hy
  use N - M
  rw [hN, hM]
  push_cast; ring

/-- The product of two integers is an integer. -/
lemma isInt_mul {x y : ℝ} (hx : isInt x) (hy : isInt y) : isInt (x * y) := by
  obtain ⟨N, hN⟩ := hx
  obtain ⟨M, hM⟩ := hy
  use N * M
  rw [hN, hM]
  push_cast; ring

/-- If `x` is an integer and `n` is a natural number, then `n * x` is an integer. -/
lemma isInt_nat_mul {x : ℝ} (hx : isInt x) (n : ℕ) : isInt (n * x) := by
  obtain ⟨N, hN⟩ := hx
  use n * N
  rw [hN]
  push_cast; ring


/-- A real number `x` is rational if there exists a positive natural number `q`
such that `q * x` is an integer. -/
def isRat (x : ℝ) : Prop := ∃ q : ℕ, q > 0 ∧ isInt (q * x)

/-- The real number `0` is rational. -/
lemma isRat_zero : isRat 0 := by
  use 1
  constructor
  · norm_num
  · simp; apply isInt_zero

/-- The real number `1` is rational. -/
lemma isRat_one : isRat 1 := by
  use 1
  constructor
  · norm_num
  · simp; norm_cast; apply isInt_one

/-- The sum of two rational numbers is rational. -/
lemma isRat_add {x y : ℝ} (hx : isRat x) (hy : isRat y) : isRat (x + y) := by
  obtain ⟨q, hq, hx⟩ := hx
  obtain ⟨r, hr, hy⟩ := hy
  use q * r
  constructor
  · positivity
  · have h : (q * r : ℕ) * (x + y) = r * (q * x) + q * (r * y) := by
      push_cast; ring
    rw [h]
    apply isInt_add (isInt_nat_mul hx r) (isInt_nat_mul hy q)

/-- The product of two rational numbers is rational. -/
lemma isRat_mul {x y : ℝ} (hx : isRat x) (hy : isRat y) : isRat (x * y) := by
  obtain ⟨q, hq, hx⟩ := hx
  obtain ⟨r, hr, hy⟩ := hy
  use q * r
  constructor
  · positivity
  · have h : (q * r : ℕ) * (x * y) = (q * x) * (r * y) := by
      push_cast; ring
    rw [h]
    apply isInt_mul hx hy

/-- The difference of two rational numbers is rational. -/
lemma isRat_sub {x y : ℝ} (hx : isRat x) (hy : isRat y) : isRat (x - y) := by
  obtain ⟨q, hq, hx⟩ := hx
  obtain ⟨r, hr, hy⟩ := hy
  use q * r
  constructor
  · positivity
  · have h : (q * r : ℕ) * (x - y) = r * (q * x) - q * (r * y) := by
      push_cast; ring
    rw [h]
    apply isInt_sub (isInt_nat_mul hx r) (isInt_nat_mul hy q)

/-- Every integer is rational. -/
lemma isRat_of_isInt {x : ℝ} (hx : isInt x) : isRat x := by
  use 1
  constructor
  · norm_num
  · norm_cast; simp; exact hx

/-- Every natural number is rational (when viewed as a real number). -/
lemma isRat_nat (n : ℕ) : isRat (n : ℝ) := by
  use 1
  constructor
  · norm_num
  · norm_cast; apply isInt_nat

/-- Every integer is rational (when viewed as a real number). -/
lemma isRat_int (n : ℤ) : isRat (n : ℝ) := by
  use 1
  constructor
  · norm_num
  · norm_cast; apply isInt_int

/-- The reciprocal of a positive natural number is rational. -/
lemma isRat_inv_nat (n : ℕ) (h : n > 0) : isRat (n : ℝ)⁻¹ := by
  use n
  constructor
  · exact h
  · have h : (n : ℝ) * (n : ℝ)⁻¹ = 1 := by
      push_cast; apply mul_inv_cancel; norm_cast; exact Nat.pos_iff_ne_zero.mp h
    rw [h]
    exact isInt_one
