import Library.Basic
noncomputable section

/- # Recap and consolidation -/

/-
  ## Geometric series

  The function `g` below defines for all `c : ℝ` and `n : ℕ` the sum
    `g c n = 1 + c + c ^ 2 + ... + c ^ (n-1)` (so there are `n` terms)
  The first few values are:
    - `g c 0 = 0` (empty sum)
    - `g c 1 = 1`
    - `g c 2 = 1 + c`
    - `g c 3 = 1 + c + c ^ 2`
  As before, we don't write parentheses around the arguments of a function, so we write
  `g c n` instead of `g(c, n)`.

  Let's start with the definition, and the two defining lemmas:
-/

def g (c : ℝ) (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => (g c n) + c ^ n

lemma g_zero (c : ℝ) : g c 0 = 0 := by rfl

lemma g_succ (c : ℝ) (n : ℕ) :
    g c (n + 1) = (g c n) + c ^ n := by rfl

/-
  From now on, you will use `g_zero` and `g_succ` to prove things about `g`.

  Let's start with some simple sanity checks to make sure this matches our
  expectations! Prove the following three lemma's using `g_zero` and `g_succ`.
-/

lemma g_one (c : ℝ) : g c 1 = 1 := by
  sorry

lemma g_two (c : ℝ) : g c 2 = 1 + c := by
  sorry

lemma g_three (c : ℝ) : g c 3 = 1 + c + c ^ 2 := by
  sorry

/-
  Calculate `g 10 4` by hand, correct the statement below, and prove it!
-/
example : g 10 4 = 2025 := by
  sorry


/-
  Now use `simple_induction` to prove that `g 1 n = n` for all `n : ℕ`.
-/
lemma g_base_one (n : ℕ) : g 1 n = n := by
  sorry

/-
  We now prove the classical formula for the sum of a geometric series. The first version
  holds for all `c : ℝ`:
    `(1 - c) * g c n = 1 - c ^ n`
  Replace the `sorry`s below with proofs.
-/
example (c : ℝ) (n : ℕ) : (1 - c) * g c n = 1 - c ^ n := by
  simple_induction n with k IH
  · sorry
  · sorry

/-
  The second version is probably more familiar, but requires the assumption that `c ≠ 1`,
  so that we can divide by `1 - c`. The following lemma will be useful.
-/
lemma one_sub_ne_zero (c : ℝ) (h : c ≠ 1) : 1 - c ≠ 0 := sub_ne_zero.mpr (id (Ne.symm h))

/-
  Now prove the second version, which says that
  ` 1 + c + c ^ 2 + ... + c ^ (n-1) = (1 - c ^ n) / (1 - c)`,
  assuming that `c ≠ 1`.

  Hint: first establish `h1 : 1 - c ≠ 0` using the lemma above,
  so that `algebra` knows it can safely handle division by `1 - c`.
-/
example (c : ℝ) (n : ℕ) (h : c ≠ 1) : g c n = (1 - c ^ n) / (1 - c) := by
  sorry




/-
  ## The harmonic sum

  We define the harmonic sum
    `s n = 1 + 1/2 + 1/3 + ... + 1/n`
  Note that there are `n` terms in the sum. The first few values are:
    `s 0 = 0` (empty sum)
    `s 1 = 1`
    `s 2 = 1 + 1/2 = 3/2`
    `s 3 = 1 + 1/2 + 1/3 = 11/6`
  We will prove that this series diverges, that is that `s n` is unbounded as
  `n` goes to infinity. But first: the definition and the two defining lemmas.
-/

def s (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => s n + 1 / (n + 1)

lemma s_zero : s 0 = 0 := by rfl

lemma s_succ (n : ℕ) : s (n + 1) = s n + 1 / (n + 1) := by rfl

/-
  Now let's do some sanity checks to make sure `s n` matches our expectations.
-/

lemma s_one : s 1 = 1 := by
  sorry

lemma s_two : s 2 = 3 / 2 := by
  sorry

lemma s_three : s 3 = 11 / 6 := by
  sorry


/-
  To practice a bit more, let's prove a simple identity for `s (n + 2)`.
  While proving this, you will often see `↑n` in the right hand window. This is
  Lean's way of telling you that it is considering `n` as a real number.
-/
example (n : ℕ) : s (n + 2) = s n + 1 / (n + 1) + 1 / (n + 2) := by
  sorry


/-
  Let us now prove some simple properties of the harmonic series `s n`.
-/
lemma s_monotone (n : ℕ) : s n ≤ s (n + 1) := by
  sorry

/-
  Now prove that `s n ≥ 0` for all `n : ℕ`. This can be done using
  `simple_induction`, and an application of the lemma `s_monotone` above.
-/
lemma s_pos (n : ℕ) : s n ≥ 0 := by
  sorry

/-
  We will prove that for every natural number `N` there is a `n` such that `s m ≥ N`
  for all `m ≥ n`. So eventually, the series will be larger than any given
  natural number.

  As a warming up, let's prove that `s m ≥ 2` for all `m ≥ 4`. This can be done
  using `induction_from_starting_point`.
-/

example (m : ℕ) (h : m ≥ 4) : s m ≥ 2 := by
  sorry


/-
  If you want to play around a bit, state and prove that:
    `s m ≥ 3` for all `m ≥ 11`
  The harmonic series grows very slowly, so this quickly goes out of hand. For example:
    `s m ≥ 10` for all `m ≥ 12367`
  I don't recommend you try to prove this now.
-/

-- instert your statement and proof here.

/-
  We now move towards proving the divergence of the harmonic series. The key
  step is theorem
    `s_double_bound n h : s (2 * n) ≥ s n + 1/2`
  for `n : ℕ` and `h : n > 0`.

  The following lemma will be useful in the proof.
-/
lemma inverse_le (a b : ℝ) (h1 : a ≤ b) (h2 : a > 0) : 1 / a ≥ 1 / b := by
  apply one_div_le_one_div_of_le h2 h1

/-
  Next we use the lemma above to establish the simple inequality
    `1 / (2 * n + 2) ≤ 1 / (2 * n + 1)`
  There is however a subtlety in the statement! Whereas `n` is a natural number,
  the division takes place in the *real numbers*. The expression `(1 : ℝ)` in
  the statement below tells Lean to consider `1` as a real number. Lean then
  automatically converts the other players in the inequality to real numbers.
-/
lemma fractions_estimate (n : ℕ) (h : n > 0) : (1 : ℝ) / (2 * n + 2) ≤ 1 / (2 * n + 1) := by
  -- First establish that `2 * n + 1 ≤ 2 * n + 2` in the real numbers using `linarith`
  have h1 : (2 * n + 1 : ℝ) ≤ (2 * n + 2 : ℝ) := by sorry
  -- Now establish that `2 * n + 1 > 0` in the real numbers using `positivity`
  have h2 : (2 * n + 1 : ℝ) > 0 := by sorry
  -- Finish the proof by applying `inverse_le` with the correct arguments.
  sorry

/-
  Examine your proof above, moving the cursor around and inspecting the right
  hand window. Pay close attention to the difference between the natural number `n`,
  and the associated real number `↑n`.
-/


/-
  Now use `fractions_estimate` to prove the lemma `s_twice_succ` below. Write
  out a detailed chain of equalities and inequalities on paper first.
-/
lemma s_twice_succ (n : ℕ) (h : n > 0) : s (2 * (n + 1)) ≥ s (2 * n) + 1 / (n + 1) := by
  sorry

/-
  Prove the following using `induction_from_starting_point` and the lemma `s_twice_succ`.
-/
lemma s_double_bound (n : ℕ) (h : n ≥ 1) : s (2 * n) ≥ s n + 1/2 := by
  induction_from_starting_point n, h with k hk IH
  · sorry
  · sorry


/-
  Finally, we establish the key lower bound! We'll need a simple lemma stating
  that `2 ^ k ≥ 1`, which can be proven (for example) using induction.
-/
lemma two_pow_ge_one (k : ℕ) : 2 ^ k ≥ 1 := by
  sorry

lemma harmonic_pow_two (n : ℕ) : s (2 ^ n) ≥ n / 2 := by
  simple_induction n with k IH
  · sorry
  · sorry


/-
   Now we can wrap up and prove divergence: for every `N : ℕ` there is an `n`
   such that `s m ≥ N` for all `m ≥ N`.

   Follow the following steps:

   1) figure out which value `N = C` to use (as a function of `n`) and start with `use C`
   2) then `intro h` to will introduce the hypothesis `m ≥ C`
   3) now you can use `induction_from_starting_point` to prove that the ineqality holds
      for all `m ≥ C`.
-/


theorem harmonic_diverges (N : ℕ) : ∃ n : ℕ, m ≥ n → s m ≥ N := by
  sorry


/-
  Congratulations! You have shown that you can use the tactics learned to prove
  some non-trivial results! In the final session, we will collaboratively prove
  a much more involved result: the irrationality of the number `e`.
-/
