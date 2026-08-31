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


theorem mathd_algebra_419 (a b : ℝ) (h₀ : a = -1) (h₁ : b = 5) : -a - b ^ 2 + 3 * (a * b) = -39 := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    enableSimp := false
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [neg_sq]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
    (add norm 0 (by grind only [Quaternion.mul_imI]))
    (add norm 0 (by grind only [Quaternion.mul_re]))
    (add norm 0 (by grind only [Quaternion.mul_imK]))
    (add norm 0 (by grind only [mul_pow]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
    (add norm 0 (by grind only [Quaternion.coe_commutes]))
    (add norm 0 (by grind only [neg_pow]))
    (add norm 0 (by grind only [sq_sub_sq]))
    (add norm 0 (by grind only [Quaternion.coe_mul_eq_smul]))
    (add norm 0 (by grind only [Quaternion.star_mul_self]))
    (add norm 0 (by grind only [sq_add_sq_mul_sq_add_sq]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imK]))
    (add norm 0 (by grind only [sq_add_mul_sq_mul_sq_add_mul_sq]))
    (add norm 0 (by grind only [euler_four_squares]))
    (add norm 0 (by grind only [Pell.Solution₁.prop_y]))
    (add norm 0 (by grind only [neg_one_sq]))
    (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
    (add unsafe 50% (by nlinarith [mul_neg_one]))
    (add unsafe 50% (by nlinarith [mul_neg]))
    (add unsafe 50% (by nlinarith [Quaternion.mul_imJ]))
    (add unsafe 50% (by nlinarith [neg_mul]))
    (add unsafe 50% (by nlinarith [Complex.I_sq]))
    (add unsafe 50% (by nlinarith [Quaternion.star_imI]))
    (add unsafe 50% (by nlinarith [neg_one_mul]))
    (add unsafe 50% (by nlinarith [Complex.I_mul_I]))
    (add unsafe 50% (by nlinarith [Quaternion.star_imJ]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
    (add unsafe 50% (by nlinarith [mul_inv]))
    (add unsafe 50% (by nlinarith [Quaternion.neg_imI]))
    (add unsafe 50% (by nlinarith [Quaternion.star_imK]))
