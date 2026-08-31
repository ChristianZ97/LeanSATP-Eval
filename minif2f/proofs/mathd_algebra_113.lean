
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


set_option maxHeartbeats 0

theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have h_rhs_eval : (7:ℝ) ^ 2 - 14 * 7 + 3 = (-46:ℝ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 600
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [aux_add]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [sum_eight_sq_mul_sum_eight_sq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [sum_four_sq_mul_sum_four_sq]))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [QuaternionGroup.xa_mul_xa]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Real.rpow_two]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Complex.two_sinh]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
      (add norm 0 (by grind only [Complex.cosh_two_mul]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))
      (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 50% (by simp only [add_sq]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))

  have h_diff_eq_square : (x:ℝ) ^ 2 - 14 * x + 3 - (7 ^ 2 - 14 * 7 + 3) = (x - 7) ^ 2 := by
    rw [h_rhs_eval]
    ring
    <;> norm_num

  have h_square_nonneg : (x - 7) ^ 2 ≥ (0:ℝ) := by
    nlinarith

  have h_main : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
    have h1 : x ^ 2 - 14 * x + 3 - (7 ^ 2 - 14 * 7 + 3) ≥ 0 := by
      rw [h_diff_eq_square]
      exact h_square_nonneg

    linarith

  exact h_main
