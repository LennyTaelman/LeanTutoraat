import Library.Basic


/- # Induction -/

/- ## Proving something holds for all natural numbres with `simple_induction` -/

/-
  Say we want to prove something for all `n : ℕ` by induction.

  The tactic `simple_induction n with k IH` creates two goals:
  - a base case: prove the statement for `n = 0`
  - an inductive step: prove the statement for `n = k + 1`,
    where the induction hypothesis `IH` is that the statement holds for `n = k`
  We then need to provide proofs for the base case and the inductive step.
-/

/-
  Below is a simple example. Note the two dots `·` after `simple_induction`.
  These indicate the two goals: base case and inductive step. Put your cursor
  after these dots to see the goals.

  Note that after the second dot, the induction hypothesis `IH` appears as a
  new hypothesis that is now available in the proof.

  Replace all the `sorry`s with proofs. Each one can be handled by a single tactic.
-/

example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · sorry
  · calc
      2 ^ (k + 1) = 2 * 2 ^ k           := by sorry
                _ ≥ 2 * (k + 1)         := by sorry -- use the induction hypothesis `IH`
                _ ≥ (k + 1) + 1         := by sorry


/-
  Now fill in the proofs of base and inductive step in the following proof.
-/

example (n : ℕ) : n ^ 2 ≥ n := by
  simple_induction n with k IH
  · sorry
  · sorry

/-
  Finally, write an induction proof for the following statement.

  To typeset the dots for base and inductive case, use `\.` Note that the proofs
  for base and inductive step are indented.

  Tip: first write a skeleton induction proof, with `sorry` for the base and inductive steps.
-/

example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  sorry



/- ## Prove something holds for all `n ≥ C` with `induction_from_starting_point` -/

/-
  Sometimes we want to prove something for all n ≥ C,
  and hence want to start induction at n = C.

  If `n` is a natural number and `h` the hypothesis that `C ≤ n`,
  then the tactic `induction_from_starting_point n, h with k hk IH`
  creates two goals:
  - a base case: prove the statement for `n = C`
  - an inductive step: prove the statement for `n = k + 1`, where
    * `hk` is the assumption that `k ≥ C`
    * `IH` is the induction hypothesis (the statement holds for `n = k`)

  Place your cursor after the two dots to see the goals. Then replace the
  sorry's with proofs.
-/

example (n : ℕ) (hn : n ≥ 2) : n ^ 2 ≥ n + 2 := by
  induction_from_starting_point n, hn with k hk IH
  · sorry
  · calc
      (k + 1) ^ 2  = k ^ 2 + 2 * k + 1 := by sorry
                 _ ≥ (k + 1) + 2       := by sorry

/-
  Now do the following one yourself
-/

example (n : ℕ) (hn : n ≥ 3) : n ^ 2 ≥ 3 * n := by
  induction_from_starting_point n, hn with k hk IH
  · sorry
  · calc
      (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by algebra
                 _ ≥  3 * (k + 1) := by linarith


/-
  One more variation. In this one, we show that `n ^ 2 ≥ n + 100` holds for if
  `n` is sufficiently large. We state it as `∃ C : ℕ, n ≥ C → n ^ 2 ≥ n + 100`,
  where the arrow `→` should be read as an implication.

  Prove this in lean, by following these steps:
  1. Figure out what value of `C` you will use. (Say `C = 5` -- which won't work!)
  2. Start the proof with `use 5`. The goal is now `n ≥ 5 → n ^ 2 ≥ n + 100`
  3. Use the tactic `intro h` to introduce the hypothesis `n ≥ 5`.
  4. Finish the proof using induction.
-/

example (n : ℕ) : ∃ C : ℕ, n ≥ C → n ^ 2 ≥ n + 100 := by
  sorry




/- # Finite sums -/

/-
  Induction is a powerful tool for proving statements about finite sums of the
  form `Σ_{i=0}^{n} a_i`.

  As a first example, let us prove that for every `n : ℕ` we have
    `1 + 2 + 4 + ... + 2 ^ (n - 1) = 2 ^ n - 1`

  First we define the left-hand side as a function
  `s : ℕ → ℕ` which maps `n` to `1 + 2 + 4 + ... + 2 ^ (n - 1)`.
-/

def s (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => s n + 2 ^ n

/-
  The above defines `s 0` to be `0` (the empty sum) and `s (n + 1)` to be `s n +
  2 ^ n`. Verify for yourself (on paper if necessary) that this indeed forces
    `s n = 1 + 2 + 4 + ... + 2 ^ (n - 1)`.

  You can ignore the precise form of the definition. All you need to know about
  `s` is
  1. `s n` is a natural number
  2. `s 0 = 0`, which is proven in the lemma `s_zero` below.
  3. `s (n + 1) = s n + 2 ^ n`, which is proven in the lemma `s_succ` below.

  In your proofs, you can *use*`rewrite [s_zero]` or `rewrite [s_succ]` to
  transform `s 0` into `0` or `s (n + 1)` into `s n + 2 ^ n`.
-/

lemma s_zero : s 0 = 0 := by rfl

lemma s_succ (n : ℕ) : s (n + 1) = s n + 2 ^ n := by rfl


/-
  We can now prove that `s n = 2 ^ n - 1` for all `n : ℕ`. We state it slightly
  differently, as `1 + s n = 2 ^ n`, to avoid having to deal with subtraction in `ℕ`.
-/


example (n : ℕ) : 1 + s n = 2 ^ n := by
  simple_induction n with k IH
  · sorry
  · calc
      1 + s (k + 1) = 1 + (s k + 2 ^ k)  := by sorry
                  _ = (1 + s k) + 2 ^ k  := by sorry
                  _ = 2 ^ k + 2 ^ k      := by sorry
                  _ = 2 ^ (k + 1)        := by sorry



/-
  The code below defines s1 : ℕ → ℕ recursively. We have
  s1 n = 1 + 2 + ... + n
-/

def s1 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => (s1 n) + (n + 1)


/-
  Again you can ignore the definition above, you'll only use the following lemmas, which
  completely determine `s1 n` for all `n : ℕ`.
-/

lemma s1_zero : s1 0 = 0 := by rfl

lemma s1_succ (n : ℕ) : s1 (n + 1) = s1 n + (n + 1) := by rfl

/-
  We now prove that `s1 n = n * (n + 1) / 2`. We state it as
  `2 * s1 n = n * (n + 1)` to avoid having to deal with division in `ℕ`.
-/


example (n : ℕ) : 2 * s1 n = n * (n + 1) := by
  simple_induction n with k IH
  · sorry
  · sorry

/-
  Let's move to squares! Consider s2 n = 1 + 2 ^ 2 + 3 ^ 2 + ... + n ^ 2.
-/

def s2 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => (s2 n) + (n + 1) ^ 2

lemma s2_zero : s2 0 = 0 := by rfl

lemma s2_succ (n : ℕ) : s2 (n + 1) = s2 n + (n + 1) ^ 2 := by rfl


/-
  Write a proof that `6 * s2 n = n * (n + 1) * (2 * n + 1)`.
-/
example (n : ℕ) : 6 * s2 n = n * (n + 1) * (2 * n + 1) := by
  sorry



/-
  Variation: prove that `3 * s2 n ≥ n ^ 3`.
-/


example (n : ℕ) : 3 * s2 n ≥ n ^ 3 := by
  sorry


-- EVERYTHING ABOVE THIS LINE HAS BEEN VERIFIED
-- TODO: add some challenges, and maybe some casting?


/-
  Challenge: prove the beautiful formula s3 n  = (s1 n) ^ 2.
  E.g. 2025 = 1^3 + 2^3 + ... + 9^3 = (1 + 2 + ... + 9)^2
-/

-- TODO: bah, no good way of doing this without first establihsing formula for s1




-- Now prove Bernoulli's inequality:

example (x : ℝ) (n : ℕ) (h : x ≥ 0) : (1 + x) ^ n ≥ 1 + n * x := by
  simple_induction n with k IH
  · -- base case: goal is `(1 + x) ^ 0 ≥ 1 + 0 * x`
    sorry
  · -- inductive step: goal is `(1 + x) ^ (k + 1) ≥ 1 + (k + 1) * x`
    calc (1 + x) ^ (k + 1) = (1 + x) * (1 + x) ^ k := by algebra
      _ ≥ (1 + x) * (1 + k * x) := by rel [IH]
      _ = 1 + (k + 1) * x +  k * x ^ 2 := by algebra
      _ ≥ 1 + (k + 1) * x := by extra


-- Note: in the right window pane you may have seen expressions like `↑k`. These
-- indicate that the natural number `k` is being considered as a real number.




/-
  ## Why did we avoid subtraction and division in the proofs above?
-/

-- Verify that `algebra` cannot prove the statement below. Why would that be?
example (n : ℕ) : (n - 1) + 1 = n := by
  sorry

/-
  In fact, in Lean the subtraction of two natural numbers is again a natural
  number. If the result would be negative, it is defined to be `0`.

  So the above statement is *false* for `n = 0`, since the left hand side is `1`.

  However, for integers (or rationals, or reals, ...) subtraction is defined as
  usual. Indeed, verify that `algebra` *can* prove the statement below.
-/

example (n : ℤ) : (n - 1) + 1 = n := by
  sorry


/-
  Exercise:
-/


example (n : ℕ) (h : n ≥ 1) : (n - 1) + 1 = n := by
  induction_from_starting_point n, h with k hk IH
  · rfl
  · algebra





/- # For later use! -/

example (N : ℕ) (h : N ≥ 1) : ∃ n : ℕ, N = n + 1 := by
  induction_from_starting_point N, h with k hk IH
  · use 0; numbers
  · obtain ⟨n, hn⟩ := IH
    use n + 1
    rewrite [hn]
    algebra
