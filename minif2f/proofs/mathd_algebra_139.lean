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


theorem mathd_algebra_139 (s : ℝ → ℝ → ℝ)
    (h₀ : ∀ x ≠ 0, ∀ y ≠ 0, s x y = (1 / y - 1 / x) / (x - y)) :
    s 3 11 = 1 / 33 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    maxGoals := 512
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 0 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by exfalso))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 90% (by norm_num [*] at *))
    (add norm 0 (by grind only [one_div]))
    (add norm 0 (by grind only [mul_one_div]))
    (add norm 0 (by grind only [div_one]))
    (add norm 0 (by grind only [div_sub']))
    (add norm 0 (by grind only [neg_div]))
    (add norm 0 (by grind only [one_div_one]))
    (add norm 0 (by grind only [one_ne_zero]))
    (add norm 0 (by grind only [div_neg]))
    (add norm 0 (by grind only [integral_one_div_of_pos]))
    (add norm 0 (by grind only [div_eq_inv_mul]))
    (add norm 0 (by grind only [WeierstrassCurve.Affine.slope_of_X_ne]))
    (add norm 0 (by grind only [WeierstrassCurve.Affine.slope]))
    (add norm 0 (by grind only [sub_div']))
    (add norm 0 (by grind only [two_ne_zero']))
    (add norm 0 (by grind only [Real.Gamma_one]))
    (add norm 0 (by grind only [Complex.Gammaℝ_one]))
    (add norm 0 (by grind only [div_self']))
    (add norm 0 (by grind only [Real.log_div]))
    (add norm 0 (by grind only [WeakFEPair.h_feq']))
    (add safe 0 (by simp only [div_self] at *))
    (add safe 0 (by simp only [div_ne_one] at *))
    (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
    (add safe 0 (by simp only [sub_div] at *))
    (add safe 0 (by simp only [div_ne_zero] at *))
    (add safe 0 (by simp only [div_mul_cancel₀] at *))
    (add safe 0 (by simp only [div_ne_one_of_ne] at *))
    (add safe 0 (by simp only [mul_div_cancel₀] at *))
    (add safe 0 (by simp only [eq_div_iff] at *))
    (add safe 0 (by simp only [div_eq_iff] at *))
    (add safe 0 (by simp only [Real.div_rpow] at *))
    (add safe 0 (by simp only [div_div] at *))
    (add safe 0 (by simp only [mul_div_assoc] at *))
