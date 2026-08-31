import Mathlib

/- Vendored verbatim from google-deepmind/formal-conjectures @ f564f8d7
(Apache-2.0): the `answer()` term elaborator (FormalConjectures/Util/Answer)
and `Real.nthRoot` (FormalConjecturesForMathlib/…/NthRoot). -/

/-- Indicates where the answer is in a problem statement. -/
syntax (name := Google.answer) "answer(" term ")" : term

namespace Google
open Lean Elab Term
/-- Indicates where the answer is in a problem statement. -/
@[term_elab answer]
def answerElab : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) => do
    mkSaveInfoAnnotation <$> postponeElabTerm (← `(by exact $a)) expectedType?
  | _ => Elab.throwUnsupportedSyntax
end Google

namespace Real
/-- `nthRoot n r` computes `ⁿ√r`; behaves as expected on negatives for odd `n`. -/
noncomputable def nthRoot (n : ℕ) (r : ℝ) : ℝ :=
  if Even n then r ^ (n⁻¹ : ℝ) else SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ)
end Real

open scoped Real
open scoped Nat
open scoped Topology
open scoped Polynomial


theorem mathd_numbertheory_321 (n : ZMod 1399) (h₁ : n = 160⁻¹) : n = 1058 := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableSimp := false
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [inv_one]))
    (add norm 0 (by grind only [Hyperreal.st_inv]))
    (add norm 0 (by grind only [TrivSqZeroExt.inv_one]))
    (add norm 0 (by grind only [inv_gold]))
    (add norm 0 (by grind only [TrivSqZeroExt.fst_inv]))
    (add norm 0 (by grind only [GroupWithZero]))
    (add norm 0 (by grind only [one_eq_inv]))
    (add norm 0 (by grind only [TrivSqZeroExt.inv_inr]))
    (add norm 0 (by grind only [TrivSqZeroExt.inv_inv]))
    (add norm 0 (by grind only [Nat.floor_one]))
    (add norm 0 (by grind only [TrivSqZeroExt.inv_inl]))
    (add norm 0 (by grind only [inv_eq_one_div]))
    (add norm 0 (by grind only [neg_inv]))
    (add norm 0 (by grind only [DualNumber.inv_eps]))
    (add norm 0 (by grind only [one_div]))
    (add norm 0 (by grind only [inv_eq_one]))
    (add norm 0 (by grind only [inv_eq_iff_eq_inv]))
    (add norm 0 (by grind only [RatFunc.single_inv]))
    (add norm 0 (by grind only [TrivSqZeroExt.fst_one]))
    (add norm 0 (by grind only [TrivSqZeroExt.mul_inv_cancel]))
    (add norm 0 (by grind only [map_inv₀]))
    (add norm 0 (by grind only [inv_neg]))
    (add norm 0 (by grind only [inv_goldConj]))
    (add norm 0 (by grind only [Nat.ceil_one]))
    (add norm 0 (by grind only [one_ne_zero]))
    (add norm 0 (by grind only [Hyperreal.Infinite.st_eq]))
    (add norm 0 (by grind only [Int.ofNat_zero]))
    (add norm 0 (by grind only [ZMod]))
    (add norm 0 (by grind only [Int.floor_one]))
    (add norm 0 (by grind only [TrivSqZeroExt.inv_mul_cancel]))
    (add norm 0 (by grind only [TrivSqZeroExt.inl_one]))
    (add norm 0 (by grind only [PadicInt.valuation_p]))
