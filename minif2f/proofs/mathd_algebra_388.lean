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


theorem mathd_algebra_388 (x y z : ℝ) (h₀ : 3 * x + 4 * y - 12 * z = 10)
    (h₁ : -2 * x - 3 * y + 9 * z = -4) : x = 14 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableSimp := false
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 90% (by norm_num [*] at *))
    (add norm 0 (by grind only [quadratic_eq_zero_iff]))
    (add norm 0 (by grind only [irrational_iff_ne_rational]))
    (add norm 0 (by grind only [Iff]))
    (add norm 0 (by grind only [two_ne_zero']))
    (add norm 0 (by grind only [IsCyclotomicExtension.Rat.Three.lambda_sq]))
    (add norm 0 (by grind only [WeierstrassCurve.Affine.Y_eq_of_Y_ne]))
    (add norm 0 (by grind only [legendreSym.eq_zero_mod_of_eq_neg_one]))
    (add norm 0 (by grind only [Pell.Solution₁.eq_one_of_x_eq_one]))
    (add norm 0 (by grind only [Quaternion.star_eq_neg]))
    (add norm 0 (by grind only [Real.sin_eq_zero_iff]))
    (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
    (add safe 0 (by simp only [div_eq_iff] at *))
    (add safe 0 (by simp only [eq_div_iff] at *))
    (add safe 0 (by nlinarith [Real.pi_pos]))
    (add unsafe 50% (by nlinarith [div_eq_one]))
    (add unsafe 50% (by nlinarith [div_eq_iff_eq_mul]))
    (add unsafe 50% (by nlinarith [div_eq_iff_eq_mul']))
    (add unsafe 50% (by nlinarith [Real.arctan_ne_mul_pi_div_two]))
    (add unsafe 50% (by nlinarith [soln_unique]))
    (add unsafe 50% (by nlinarith [Ideal.toCotangent_eq]))
    (add unsafe 50% (by nlinarith [div_ne_one]))
    (add unsafe 50% (by nlinarith [neg_div]))
    (add unsafe 50% (by nlinarith [mul_self_eq_one_iff]))
    (add unsafe 50% (by nlinarith [div_ne_one_of_ne]))
    (add unsafe 50% (by nlinarith [div_lt_iff]))
    (add unsafe 50% (by nlinarith [eq_of_div_eq_one]))
    (add unsafe 50% (by nlinarith [Real.Angle.coe_sub]))
    (add unsafe 50% (by nlinarith [lt_div_iff]))
    (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
    (add unsafe 50% (by nlinarith [mul_left_inj']))
    (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
