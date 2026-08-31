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


theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    useSimpAll := false
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by bound))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 90% (by norm_num [*] at *))
    (add norm 0 (by grind only [inv_eq_iff_eq_inv]))
    (add norm 0 (by grind only [quadratic_eq_zero_iff]))
    (add norm 0 (by grind only [inv_eq_one]))
    (add norm 0 (by grind only [neg_div]))
    (add norm 0 (by grind only [Real.pi_ne_zero]))
    (add norm 0 (by grind only [Quaternion.star_eq_self]))
    (add norm 0 (by grind only [Quaternion.star_eq_neg]))
    (add norm 0 (by grind only [mul_self_eq_one_iff]))
    (add norm 0 (by grind only [neg_eq]))
    (add norm 0 (by grind only [Complex.I_ne_zero]))
    (add norm 0 (by grind only [eq_neg_self_iff]))
    (add norm 0 (by grind only [div_neg]))
    (add norm 0 (by grind only [two_ne_zero']))
    (add norm 0 (by grind only [Complex.sin_eq_zero_iff]))
    (add norm 0 (by grind only [eq_false_intro]))
    (add norm 0 (by grind only [Complex.cpow_neg_one]))
    (add norm 0 (by grind only [Complex.ofReal_inj]))
    (add norm 0 (by grind only [Quaternion.ext_iff]))
    (add norm 0 (by grind only [Real.sin_eq_zero_iff]))
    (add safe 0 (by simp only [div_eq_iff] at *))
    (add safe 0 (by simp only [eq_div_iff] at *))
    (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
    (add unsafe 50% (by nlinarith [div_eq_one]))
    (add unsafe 50% (by nlinarith [mul_eq_one_iff_eq_inv]))
    (add unsafe 50% (by nlinarith [eq_inv_iff_mul_eq_one]))
    (add unsafe 50% (by nlinarith [div_eq_iff_eq_mul]))
    (add unsafe 50% (by nlinarith [inv_eq_iff_mul_eq_one]))
    (add unsafe 50% (by nlinarith [div_eq_iff_eq_mul']))
    (add unsafe 50% (by nlinarith [Complex.arctan]))
    (add unsafe 50% (by nlinarith [mul_neg_one]))
    (add unsafe 50% (by nlinarith [QuaternionAlgebra.star_eq_neg]))
    (add unsafe 50% (by nlinarith [groupCohomology.mem_oneCocycles_def]))
