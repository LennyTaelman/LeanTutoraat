import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
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
  add custom "exercise" command, behaving like "example"
-/

open Lean.Elab.Command in

elab "exercise" hyps:bracketedBinder* ":" thm:term ":=" prf:term : command
  => do elabCommand (← `(command|example $(hyps):bracketedBinder* : $thm := $prf))
