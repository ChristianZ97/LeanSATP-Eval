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


theorem mathd_numbertheory_207 : 8 * 9 ^ 2 + 5 * 9 + 2 = 695 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    maxGoals := 512
    enableSimp := false
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by bound))
    (add norm 100 (by exfalso))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 1 (by ring_nf at *))
    (add safe 100 (by field_simp [*] at *))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [euler_four_squares]))
    (add norm 0 (by grind only [sq_sub_sq]))
    (add norm 0 (by grind only [add_sq]))
    (add norm 0 (by grind only [sum_four_sq_mul_sum_four_sq]))
    (add norm 0 (by grind only [sum_eight_sq_mul_sum_eight_sq]))
    (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
    (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
    (add norm 0 (by grind only [sq_abs]))
    (add norm 0 (by grind only [Real.cosh_sq']))
    (add norm 0 (by grind only [two_mul_le_add_sq]))
    (add norm 0 (by grind only [Complex.sq_abs]))
    (add norm 0 (by grind only [Quaternion.normSq_def']))
    (add norm 0 (by grind only [sq_nonneg]))
    (add norm 0 (by grind only [sub_sq]))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [Real.cosh_sq]))
    (add norm 0 (by grind only [Real.cosh_two_mul]))
    (add norm 0 (by grind only [even_two_mul]))
    (add norm 0 (by grind only [Int.le_self_sq]))
    (add norm 0 (by grind only [UpperHalfPlane.dist_coe_center_sq]))
    (add norm 0 (by grind only [sq_lt_sq]))
    (add norm 0 (by grind only [Real.sinh_two_mul]))
    (add unsafe 50% (by simp only [sq_add_sq_mul]))
    (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
    (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
    (add unsafe 90% (by simp only [pow_two] at *))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
    (add unsafe 50% (by simp only [Int.sq_eq_one_of_sq_le_three]))
    (add unsafe 90% (by simp only [Real.rpow_two] at *))
