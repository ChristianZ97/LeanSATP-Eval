
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

theorem mathd_algebra_17 (a : ℝ)
    (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) :
    a = 8 := by
  -- Step 2: sqrt(16 + 16*a) = sqrt(16*(1+a))
  have h_step2 : Real.sqrt (16 + 16 * a) = Real.sqrt (16 * (1 + a)) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 60
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul_self_eq_abs]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [Real.cos_half]))
      (add norm 0 (by grind only [Real.sqrt_one]))
      (add norm 0 (by grind only [EuclideanSpace.dist_eq]))
      (add norm 0 (by grind only [Real.sqrt_inv]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [integral_gaussian]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [Real.arccos_eq_arcsin]))
      (add norm 0 (by grind only [Real.sqrt_div]))
      (add norm 0 (by grind only [Real.abs_sin_half]))
      (add norm 0 (by grind only [Real.sin_half_eq_sqrt]))
      (add norm 0 (by grind only [Complex.abs_def]))
      (add norm 0 (by grind only [Real.div_sqrt]))
      (add norm 0 (by grind only [Complex.abs_add_mul_I]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_coe_center]))
      (add norm 0 (by grind only [norm_eq_sqrt_inner]))
      (add norm 0 (by grind only [Complex.abs_apply]))
      (add norm 0 (by grind only [integral_sqrt_one_sub_sq]))
      (add norm 0 (by grind only [Real.arcsin_eq_arccos]))
      (add norm 0 (by grind only [norm_eq_sqrt_real_inner]))
      (add norm 0 (by grind only [Complex.abs_le_sqrt_two_mul_max]))

  -- Step 3: sqrt(16*(1+a)) = 4*sqrt(1+a)
  have h_step3 : Real.sqrt (16 * (1 + a)) = 4 * Real.sqrt (1 + a) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [Real.rpow_two]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [integral_gaussian]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [Real.cos_half]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [Quaternion.star_eq_two_re_sub]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [EuclideanSpace.dist_eq]))
      (add norm 0 (by grind only [Real.sqrt_mul_self_eq_abs]))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add norm 0 (by grind only [parallelogram_law_with_norm]))

  -- Step 4: sqrt(4 + 4*sqrt(1+a)) = sqrt(4*(1+sqrt(1+a)))
  have h_step4 : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) = Real.sqrt (4 * (1 + Real.sqrt (1 + a))) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [Real.sqrt_mul_self_eq_abs]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [Real.cos_half]))
      (add norm 0 (by grind only [Real.sqrt_inv]))
      (add norm 0 (by grind only [EuclideanSpace.dist_eq]))
      (add norm 0 (by grind only [Real.arccos_eq_arcsin]))
      (add norm 0 (by grind only [mul_self_nonneg]))
      (add norm 0 (by grind only [integral_gaussian]))
      (add norm 0 (by grind only [norm_add_sq]))
      (add norm 0 (by grind only [Real.abs_sin_half]))
      (add norm 0 (by grind only [Real.sqrt_one]))
      (add norm 0 (by grind only [Real.sqrt_pos]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Complex.abs_def]))
      (add norm 0 (by grind only [Complex.abs_add_mul_I]))
      (add norm 0 (by grind only [Real.div_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt_iff]))
      (add norm 0 (by grind only [norm_eq_sqrt_inner]))
      (add norm 0 (by grind only [Real.sin_half_eq_sqrt]))
      (add norm 0 (by grind only [aux_add]))
      (add norm 0 (by grind only [sq_abs]))

  -- Step 5: sqrt(4*(1+sqrt(1+a))) = 2*sqrt(1+sqrt(1+a))
  have h_step5 : Real.sqrt (4 * (1 + Real.sqrt (1 + a))) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.rpow_two]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [Quaternion.star_eq_two_re_sub]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [integral_gaussian]))
      (add norm 0 (by grind only [ENNReal.rpow_two]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  -- Combine steps to simplify LHS of h₀
  -- Original: sqrt(4 + sqrt(16 + 16*a)) + sqrt(1 + sqrt(1+a)) = 6
  -- Becomes: 2*sqrt(1 + sqrt(1+a)) + sqrt(1 + sqrt(1+a)) = 6

  let lhs_term1 := Real.sqrt (4 + Real.sqrt (16 + 16 * a))
  let lhs_term2 := Real.sqrt (1 + Real.sqrt (1 + a))

  have h_simplify1 : lhs_term1 = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    clear * - h_step2 h_step3 h_step4 h_step5
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_self_nonneg]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [TsirelsonInequality.tsirelson_inequality_aux]))
      (add norm 0 (by grind only [Quaternion.star_eq_two_re_sub]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [conjugate_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt_iff]))
      (add norm 0 (by grind only [Quaternion.self_mul_star]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [Quaternion.mul_star_eq_coe]))
      (add norm 0 (by grind only [Pell.Solution₁.coe_mk]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  have h_simplify_eq : 2 * Real.sqrt (1 + Real.sqrt (1 + a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by
    clear * - h₀ h_simplify1
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.rpow_two]))
      (add norm 0 (by grind only [mul_self_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star']))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  -- Step 6: 3*sqrt(1+sqrt(1+a)) = 6
  have h_step6 : 3 * Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by
    clear * - h_simplify_eq
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [mul_self_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Real.sqrt_pos]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))

  -- Step 7: sqrt(1+sqrt(1+a)) = 2
  have h_step7 : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by
    clear * - h_step6
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [Real.sqrt_eq_iff_sq_eq]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [NNReal.rpow_two]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [ENNReal.rpow_two]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [mul_self_nonneg]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  -- Step 8: 1 + sqrt(1+a) = 4
  have h_step8 : 1 + Real.sqrt (1 + a) = 4 := by
    clear * - h_step7
    have ht := h_step7
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity)] at h_step7
    · nlinarith [Real.sqrt_nonneg (1 + a)]
    · norm_num

  -- Step 9: sqrt(1+a) = 3
  have h_step9 : Real.sqrt (1 + a) = 3 := by
    clear * - h_step8
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_eq_iff_sq_eq]))
      (add norm 0 (by grind only [Real.arccos_eq_arcsin]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_inj]))
      (add norm 0 (by grind only [Real.sqrt_one]))
      (add norm 0 (by grind only [norm_add_eq_sqrt_iff_real_inner_eq_zero]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]))
      (add norm 0 (by grind only [mul_self_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
      (add norm 0 (by grind only [Real.arctan_eq_arccos]))
      (add norm 0 (by grind only [Real.sqrt_eq_iff_mul_self_eq_of_pos]))
      (add norm 0 (by grind only [norm_add_sq_eq_norm_sq_add_norm_sq_real]))
      (add norm 0 (by grind only [Real.arccos_eq_arctan]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [mul_self_inj_of_nonneg]))
      (add norm 0 (by grind only [Real.sin_arccos]))
      (add norm 0 (by grind only [Real.sqrt_eq_iff_mul_self_eq]))
      (add norm 0 (by grind only [Real.sqrt_pos]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [norm_add_mul_self]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [Real.arcsin_eq_arccos]))

  -- Step 10: 1 + a = 9
  have h_step10 : 1 + a = 9 := by
    clear * - h_step9
    rw [@Real.sqrt_eq_iff_mul_self_eq _ _] at h_step9
    · linarith <;> ring
    · exact le_of_lt $ Real.sqrt_pos.1 (by linarith)
    · linarith [Real.sqrt_pos.1 <| by linarith]

  -- Step 11: a = 8
  have h_step11 : a = 8 := by
    clear * - h_step10
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
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_eq_sq_iff_eq_or_eq_neg]))
      (add norm 0 (by grind only [mul_self_eq_one_iff]))
      (add norm 0 (by grind only [mul_eq_one_iff']))
      (add norm 0 (by grind only [mul_right_eq_self]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_left_eq_self]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [Quaternion.star_eq_self]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [inv_eq_iff_mul_eq_one]))
      (add norm 0 (by grind only [mul_eq_one_iff_eq_inv]))
      (add norm 0 (by grind only [eq_inv_iff_mul_eq_one]))
      (add norm 0 (by grind only [add_self_eq_zero]))
      (add norm 0 (by grind only [eq_false_intro]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Quaternion.star_eq_neg]))
      (add norm 0 (by grind only [mul_eq_one]))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [quadratic_eq_zero_iff]))
      (add norm 0 (by grind only [self_eq_mul_left]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Pell.Solution₁.eq_one_of_x_eq_one]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Polynomial.X_pow_sub_X_sub_one_irreducible_aux]))
      (add norm 0 (by grind only [mul_self_eq_zero]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [mul_left_inj]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_eq_neg]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add unsafe 90% (by simp only [pow_two] at *))

  exact h_step11
