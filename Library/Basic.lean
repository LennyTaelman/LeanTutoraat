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

macro "linarith" linarithArgsRest : tactic => `(tactic | fail "linarith tactic disabled")
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


/--
Configure the environment with the right options and attributes
for the book *The Mechanics of Proof*.

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
elab "math2001_init" : command => do
  trySetOptions #[
    ⟨`push_neg.use_distrib, true⟩
  ]
  tryEraseAttrs #[
    ⟨`simp, #[`ne_eq]⟩,
    ⟨`ext, #[`Prod.ext]⟩,
    ⟨`instance, #[`Int.instDivInt_1,`Int.instDivInt, `Nat.instDivNat]⟩,
    ⟨`norm_num, #[`Mathlib.Meta.NormNum.evalNatDvd, `Mathlib.Meta.NormNum.evalIntDvd]⟩
  ]


/-
  Trigonometry
-/

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


/-
  Custom delaborator to print `(sin x) ^ n` and `(cos x) ^ n` in stead
  of `sin x ^ n` and `cos x ^ n`
-/

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


/-
  Custom `exercise` command as alternative to `example`
-/

open Lean.Elab.Command in

elab "exercise" hyps:bracketedBinder* ":" thm:term ":=" prf:term : command
  => do elabCommand (← `(command|example $(hyps):bracketedBinder* : $thm := $prf))


-- issue: sorry linter will underline entire declaration

example : 1 + 1 = 2 := by sorry

exercise : 1 + 1 = 2 := by sorry
