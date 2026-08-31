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


theorem mathd_algebra_176 (x : ℝ) : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableSimp := false
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 50% (by ring_nf at *))
    (add norm 0 (by rw [Quaternion.coe_mul]))
    (add norm 0 (by grind only [sq_sub_sq]))
    (add norm 0 (by grind only [euler_four_squares]))
    (add norm 0 (by grind only [Quaternion.normSq_coe]))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [Quaternion.coe_commutes]))
    (add norm 0 (by rw [Quaternion.exp_coe]))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
    (add norm 0 (by rw [Quaternion.star_coe]))
    (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
    (add norm 0 (by grind only [Quaternion.inner_self]))
    (add norm 0 (by grind only [Quaternion.normSq_smul]))
    (add norm 0 (by grind only [integral_gaussian]))
    (add norm 0 (by grind only [Quaternion.normSq_ratCast]))
    (add norm 0 (by grind only [sq_abs]))
    (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
    (add norm 0 (by grind only [Quaternion.coeComplex_mul]))
    (add norm 0 (by grind only [Quaternion.coe_mul_eq_smul]))
    (add norm 0 (by grind only [Quaternion.normSq_def']))
    (add norm 0 (by grind only [Quaternion.normSq_natCast]))
    (add norm 0 (by grind only [Real.sqrt_sq]))
    (add norm 0 (by grind only [norm_add_sq_real]))
    (add norm 0 (by grind only [mul_pow]))
    (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
    (add norm 0 (by grind only [Complex.ofReal_pow]))
    (add norm 0 (by grind only [Quaternion.normSq_exp]))
    (add norm 0 (by grind only [Quaternion.normSq]))
    (add unsafe 50% (by simp only [sq_add_sq_mul]))
    (add unsafe 90% (by simp only [Real.rpow_two] at *))
    (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
    (add unsafe 90% (by simp only [pow_two] at *))
