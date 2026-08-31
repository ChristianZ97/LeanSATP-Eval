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


theorem mathd_algebra_440 (x : ℝ) (h₀ : 3 / 2 / 3 = x / 10) : x = 5 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    maxGoals := 512
    enableSimp := false
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 1 (by field_simp [*] at *))
    (add norm 1 (by norm_num [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by ext))
    (add safe 0 (by split))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [mul_one_div]))
    (add norm 0 (by grind only [one_div]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [neg_div]))
    (add norm 0 (by grind only [CircleDeg1Lift.transnumAuxSeq]))
    (add norm 0 (by grind only [div_sub']))
    (add safe 0 (by simp only [div_self] at *))
    (add safe 0 (by simp only [sub_div] at *))
    (add safe 0 (by simp only [eq_div_iff] at *))
    (add safe 0 (by simp only [div_eq_iff] at *))
    (add safe 0 (by simp only [div_mul_cancel₀] at *))
    (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
    (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
    (add safe 0 (by simp only [mul_div_cancel₀] at *))
    (add safe 0 (by simp only [two_ne_zero'] at *))
    (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
    (add safe 0 (by simp only [mul_div_assoc] at *))
    (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
    (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))
    (add safe 0 (by simp only [div_div] at *))
    (add safe 0 (by simp only [mul_div] at *))
    (add safe 0 (by simp only [mul_div_mul_left] at *))
    (add safe 0 (by simp only [add_div] at *))
    (add safe 0 (by simp only [div_ne_zero] at *))
    (add safe 0 (by simp only [Complex.ofReal_div] at *))
    (add safe 0 (by simp only [Rat.num_div_den] at *))
    (add safe 0 (by simp only [Real.log_div] at *))
    (add safe 0 (by simp only [Quaternion.coe_div] at *))
    (add safe 0 (by simp only [div_left_inj'] at *))
    (add safe 0 (by simp only [div_right_comm] at *))
    (add safe 0 (by simp only [mul_div_mul_right] at *))
    (add safe 0 (by simp only [HurwitzZeta.completedHurwitzZetaEven_eq] at *))
