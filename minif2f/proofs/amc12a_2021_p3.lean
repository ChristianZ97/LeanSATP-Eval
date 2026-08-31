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


theorem amc12a_2021_p3 (x y : ℕ) (h₀ : x + y = 17402) (h₁ : 10 ∣ x) (h₂ : x / 10 = y) :
    ↑x - ↑y = (14238 : ℤ) := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    useDefaultSimpSet := false
    })
    (add norm 0 (by ring))
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [mul_div_cancel_right]))
    (add norm 0 (by grind only [mul_div_cancel_left]))
    (add norm 0 (by grind only [div_self']))
    (add norm 0 (by grind only [div_eq_one]))
    (add norm 0 (by grind only [AddConstMapClass.map_sub_const]))
    (add norm 0 (by grind only [mul_div_cancel]))
    (add norm 0 (by grind only [WeakFEPair.functional_equation]))
    (add norm 0 (by grind only [gosperCatalan]))
    (add norm 0 (by grind only [LinearPMap.map_sub]))
    (add norm 0 (by grind only [ContinuousAlternatingMap.sub_apply]))
    (add norm 0 (by grind only [tsub_div]))
    (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
    (add norm 0 (by grind only [AddConstMapClass.map_sub_one]))
    (add norm 0 (by grind only [LinearMap.BilinForm.sub_left]))
    (add norm 0 (by grind only [LinearMap.BilinForm.sub_right]))
    (add norm 0 (by grind only [AddConstMapClass.map_sub_nsmul]))
    (add norm 0 (by grind only [div_sub_div_same]))
    (add norm 0 (by grind only [CompactlySupportedContinuousMap.sub_apply]))
    (add safe 1 (by simp_all only [div_eq_iff_eq_mul]))
    (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
    (add safe 0 (by simp only [eq_div_iff] at *))
    (add safe 0 (by simp only [div_mul] at *))
    (add safe 0 (by simp only [sub_div] at *))
    (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
    (add safe 0 (by simp only [div_div] at *))
    (add safe 0 (by simp only [div_eq_iff] at *))
    (add safe 0 (by simp only [mul_div] at *))
    (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))
    (add safe 0 (by simp only [div_self] at *))
    (add safe 1 (by simp_all only [div_eq_iff_eq_mul']))
    (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
    (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))
