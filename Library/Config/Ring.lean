/- Copyright (c) 2023 Heather Macbeth. All rights reserved. -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! In this file we let `ring` silently operate as `ring_nf` (the recursive normalization form of
`ring`) when (1) it is used in conv mode, or (2) it is used terminally.  We also make it fail for
nonterminal use. -/

macro_rules | `(conv | ring) => `(conv | ring_nf)
macro "ring" : tactic => `(tactic | first | (ring_nf; done) | ring1)

/--
The `algebra` tactic attempts to prove algebraic identities involving addition, multiplication,
subtraction, and division.
-/
macro "algebra" : tactic =>
  `(tactic | first |
    (push_cast; first | ring | (field_simp; ring) | (field_simp; done)) |
    fail "algebra failed. Perhaps the goal is not an algebraic identity, or the identity is false?")

-- macro "algebra" : tactic => `(tactic | first | ring | field_simp | (field_simp; ring))
