import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Library.Config.Constructor
import Library.Config.Contradiction
import Library.Config.ExistsDelaborator
import Library.Config.Initialize
import Library.Config.Ring
import Library.Config.Use
import Library.Theory.Comparison
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Extra.Basic
import Library.Tactic.Induction
import Library.Tactic.Numbers.Basic
import Library.Tactic.Obtain
import Library.Tactic.TruthTable

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r


macro "nlinarith" linarithArgsRest : tactic => `(tactic | fail "nlinarith tactic disabled")
macro "linarith!" linarithArgsRest : tactic => `(tactic | fail "linarith! tactic disabled")
macro "nlinarith!" linarithArgsRest : tactic => `(tactic | fail "nlinarith! tactic disabled")
macro "polyrith" : tactic => `(tactic | fail "polyrith tactic disabled")
macro "decide" : tactic => `(tactic | fail "decide tactic disabled")
macro "aesop" : tactic => `(tactic | fail "aesop tactic disabled")
macro "tauto" : tactic => `(tactic | fail "tauto tactic disabled")

open Lean.Parser.Tactic in
macro "simp" : tactic => `(tactic|
    simp only [one_mul, mul_one, zero_mul, mul_zero,
      add_zero, zero_add, _root_.pow_zero, div_one, sub_self,
      pow_one, one_pow,
      sub_lt_self_iff])


-- macro "linarith" : tactic => `(tactic|
--     linarith (config := { splitHypotheses := true, discharger :=  simp }))



/--
This if from *The Mechanics of Proof*. Might not need this...

Tries to perform essentially the following:

```
set_option push_neg.use_distrib true

attribute [-simp] ne_eq
attribute [-ext] Prod.ext
attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
attribute [-norm_num] Mathlib.Meta.NormNum.evalNatDvd
  Mathlib.Meta.NormNum.evalIntDvd
```
-/
elab "tutoraat_init" : command => do
  trySetOptions #[
    ⟨`push_neg.use_distrib, true⟩
  ]
  tryEraseAttrs #[
    ⟨`simp, #[`ne_eq]⟩,
    ⟨`ext, #[`Prod.ext]⟩,
    ⟨`instance, #[`Int.instDivInt_1,`Int.instDivInt, `Nat.instDivNat]⟩,
    ⟨`norm_num, #[`Mathlib.Meta.NormNum.evalNatDvd, `Mathlib.Meta.NormNum.evalIntDvd]⟩
  ]
  -- macro "linarith" linarithArgsRest : tactic => `(tactic | fail "linarith tactic disabled")

/-
  Trigonometry
-/

namespace Tutoraat
noncomputable def sin (x : ℝ) : ℝ := Real.sin x
noncomputable def cos (x : ℝ) : ℝ := Real.cos x
noncomputable def π : ℝ := Real.pi

lemma sin_zero : sin 0 = 0 := Real.sin_zero
lemma cos_zero : cos 0 = 1 := Real.cos_zero
lemma sin_pi : sin π = 0 := Real.sin_pi
lemma cos_pi : cos π = -1 := Real.cos_pi
lemma sin_add (x y : ℝ) : sin (x + y) = sin x * cos y + cos x * sin y := Real.sin_add x y
lemma cos_add (x y : ℝ) : cos (x + y) = cos x * cos y - sin x * sin y := Real.cos_add x y
lemma sin_sq_add_cos_sq (x : ℝ) : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
end Tutoraat

export Tutoraat (sin_zero cos_zero sin_pi cos_pi sin_add cos_add sin_sq_add_cos_sq)

/-
  Group theory
-/

-- namespace Tutoraat
-- /-- In any group `a * a⁻¹ = 1 ` -/
-- lemma mul_right_inv {G : Type} [Group G] (a : G) : a * a⁻¹ = 1 := _root_.mul_right_inv a
-- lemma one_mul {G : Type} [Group G] (a : G) : 1 * a = a := _root_.one_mul a
-- lemma mul_one {G : Type} [Group G] (a : G) : a * 1 = a := _root_.mul_one a
-- lemma mul_left_inv {G : Type} [Group G] (a : G) : a⁻¹ * a = 1 := _root_.mul_left_inv a
-- lemma mul_assoc {G : Type} [Group G] (a b c : G) : (a * b) * c = a * (b * c) := _root_.mul_assoc a b c

-- end Tutoraat

-- export Tutoraat (mul_right_inv one_mul mul_one mul_left_inv mul_assoc)


/-
  Custom docstrings for example proof
-/

namespace Tutoraat

/-- If the difference `b - a` is non-negative, then `a ≤ b`. -/
lemma le_of_diff_nonneg (a b : ℝ) (h : 0 ≤ b - a) : a ≤ b := by
  exact sub_nonneg.mp h

/-- The square of a real number is non-negative. -/
lemma zero_le_sq (a : ℝ) : 0 ≤ a ^ 2 := _root_.sq_nonneg a

end Tutoraat

export Tutoraat (le_of_diff_nonneg zero_le_sq)


/-
  Custom docstrings for tactics
-/

/--
The `rfl` tactic proves goals of the form `a = a`, `a ≤ a`, `a ↔ a`, etc. It
stands for "reflexivity". Example:

```
example (a : ℝ) : a ≤ a := by
  rfl
```
-/
macro "rfl" : tactic => `(tactic| rfl)

/--
The `rewrite [h]` tactic replaces occurrences of the left-hand side of the equality or equivalence `h` in the goal with the right-hand side.
You can use `rewrite [← h]` to replace the right-hand side with the left-hand side instead.
-/
macro "rewrite" "[" hs:Lean.Parser.Tactic.rwRule,* "]" : tactic => `(tactic| rewrite [$hs,*])


/--
The `sorry` tactic admits the current goal without proof. It is used as a placeholder when you want to skip a proof and continue working on the rest of the file.
-/
macro "sorry" : tactic => `(tactic| sorry)



/--
  The `linarith` tactic tries to prove a goal of the form `a ≤ b` or `a < b` or
  `a = b` which follows from a linear manipulation of the available hypotheses.
  It may be helpful to add hypotheses using the `have` tactic.
-/
macro "linarith" : tactic => `(tactic | first | linarith | norm_cast <;> done | (norm_cast; linarith) )

/--
The `apply` tactic applies a lemma to the current goal, generating new subgoals
for each of its hypotheses.
-/
macro "apply" h:term : tactic => `(tactic| apply $h)

/--
The `have` tactic introduces a new hypothesis. Use `have h : P := by proof` to
prove statement `P` and give it the name `h`, which you can then use in the rest of the proof.
-/
macro "have" h:ident " : " p:term " := " proof:term : tactic => `(tactic| have $h : $p := $proof)


/-
  Custom delaborator to print `(sin x) ^ n` and `(cos x) ^ n` in stead
  of `sin x ^ n` and `cos x ^ n`
-/

open Tutoraat

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.HPow.hPow]
def delabTrigPow : Delab := do
  let e ← getExpr
  guard (e.isAppOfArity ``HPow.hPow 6)

  let base := e.getArg! 4
  let exp := e.getArg! 5

  -- Check if base is a (local) sin or cos application
  guard (base.isAppOfArity ``sin 1 || base.isAppOfArity ``cos 1)

  let baseStx ← delab base
  let expStx ← delab exp
  `(($baseStx) ^ $expStx)


#check sin_sq_add_cos_sq -- (sin x) ^ 2 + (cos x) ^ 2 = 1
#check 4 ^ 2 -- 4 ^ 2



/-
  Custom delaborator to print `(a + b) + c` in stead of `a + b + c`
-/
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.HAdd.hAdd]
def delabAddWithParens : Delab := do
  let e ← getExpr
  guard (e.isAppOfArity ``HAdd.hAdd 6)

  let lhs := e.getArg! 4
  let rhs := e.getArg! 5
  guard (lhs.isAppOfArity ``HAdd.hAdd 6)

  let lhsStx ← delab lhs
  let rhsStx ← delab rhs
  `(($lhsStx) + $rhsStx)


/-
  Custom delaborator to print `(a * b) * c` in stead of `a * b * c`
-/
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.HMul.hMul]
def delabMulWithParens : Delab := do
  let e ← getExpr
  guard (e.isAppOfArity ``HMul.hMul 6)

  let lhs := e.getArg! 4
  let rhs := e.getArg! 5
  guard (lhs.isAppOfArity ``HMul.hMul 6)

  let lhsStx ← delab lhs
  let rhsStx ← delab rhs
  `(($lhsStx) * $rhsStx)
