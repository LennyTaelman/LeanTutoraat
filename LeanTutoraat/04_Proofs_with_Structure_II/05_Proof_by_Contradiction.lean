/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · sorry

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  sorry


example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · sorry
  · sorry




example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  sorry



/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  sorry

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  sorry


example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  sorry
