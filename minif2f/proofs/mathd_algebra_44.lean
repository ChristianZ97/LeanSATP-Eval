
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

theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  have h2 : s = 9 - 2 * (3 * s + 1) := by
    clear * - h₀ h₁
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 120
      maxNormIterations := 60
      maxGoals := 512
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [div_mul]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_div_cancel₀]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [div_eq_iff_eq_mul]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [lt_div_iff_mul_lt]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))

  have h3 : s = 9 - (6 * s + 2) := by
    clear * - h2
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 600
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
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [add_self_div_two]))
      (add norm 0 (by grind only [sub_half]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [add_halves']))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [sub_self_div_two]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 1 (by simp_all [lt_div_iff_mul_lt]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Real.Angle.coe_sub]))
      (add norm 0 (by grind only [half_sub]))
      (add norm 0 (by grind only [div_lt_iff_lt_mul']))
      (add safe 0 (by simp only [div_mul] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add unsafe 50% (by grind only [div_eq_iff_eq_mul]))
      (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))

  have h4 : s = 7 - 6 * s := by
    clear * - h3
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
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [add_self_div_two]))
      (add norm 0 (by grind only [sub_half]))
      (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux4]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [add_halves']))
      (add norm 0 (by grind only [Real.Angle.coe_sub]))
      (add norm 0 (by grind only [sub_self_div_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Real.cos_add_cos]))
      (add norm 0 (by grind only [parallelogram_law_with_norm]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 1 (by simp_all [div_lt_iff_lt_mul']))
      (add norm 0 (by grind only [half_sub]))
      (add norm 1 (by simp_all [lt_div_iff_mul_lt]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
      (add safe 0 (by simp only [div_mul] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by grind only [div_eq_iff_eq_mul]))
      (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))
      (add unsafe 50% (by grind only [div_eq_iff_eq_mul']))

  have h5 : s + 6 * s = 7 := by
    clear * - h4
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_eq_iff_eq_mul]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [div_mul]))
      (add norm 0 (by grind only [Real.Angle.coe_sub]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [div_eq_iff_eq_mul']))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux4]))
      (add norm 0 (by grind only [Quaternion.coe_sub]))
      (add norm 0 (by grind only [add_self_div_two]))
      (add norm 0 (by grind only [add_halves']))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
      (add norm 0 (by grind only [Real.cos_add_cos]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [parallelogram_law_with_norm]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [QuaternionGroup.xa_mul_xa]))
      (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux3]))
      (add norm 0 (by grind only [Real.sin_sub_sin]))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))

  have h6 : 7 * s = 7 := by
    clear * - h5
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Real.Angle.coe_two_pi]))
      (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
      (add norm 0 (by grind only [Real.rpow_two]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Quaternion.star_eq_two_re_sub]))
      (add norm 0 (by grind only [Complex.two_cosh]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Quaternion.sq_eq_neg_normSq]))
      (add norm 0 (by grind only [Quaternion.coe_mul]))
      (add norm 0 (by grind only [integral_gaussian]))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.sqrt_eq_iff_sq_eq]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [Complex.two_sinh]))

  have h7 : s = 1 := by
    clear * - h6
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 256
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Quaternion.star_eq_self]))
      (add norm 0 (by grind only [Quaternion.coe_inj]))
      (add norm 0 (by grind only [Complex.ofReal_inj]))
      (add norm 0 (by grind only [Quaternion.star_eq_neg]))
      (add norm 0 (by grind only [Hyperreal.coe_eq_coe]))
      (add norm 0 (by grind only [mul_left_inj']))
      (add norm 0 (by grind only [mul_eq_one_iff']))
      (add norm 0 (by grind only [mul_eq_mul_left_iff]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [mul_eq_left₀]))
      (add norm 0 (by grind only [Quaternion.normSq_eq_zero]))
      (add norm 0 (by grind only [UpperHalfPlane.ext_iff]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_eq_self]))
      (add norm 0 (by grind only [Quaternion.ext_iff]))
      (add norm 0 (by grind only [Real.sqrt_eq_iff_sq_eq]))
      (add norm 0 (by grind only [Complex.exp_eq_exp_iff_exp_sub_eq_one]))
      (add norm 0 (by grind only [quadratic_eq_zero_iff]))
      (add norm 0 (by grind only [mul_self_eq_one_iff]))
      (add norm 0 (by grind only [Real.sqrt_eq_iff_mul_self_eq_of_pos]))
      (add norm 0 (by grind only [circleMap_eq_center_iff]))
      (add norm 0 (by grind only [Quaternion.sq_eq_neg_normSq]))
      (add norm 0 (by grind only [Complex.arg_ofReal_of_nonneg]))
      (add norm 0 (by grind only [Complex.exp_eq_one_iff]))
      (add norm 0 (by grind only [sq_eq_sq_iff_eq_or_eq_neg]))
      (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
      (add norm 0 (by grind only [mul_eq_zero]))
      (add norm 0 (by grind only [mul_right_inj']))
      (add norm 0 (by grind only [mul_eq_one]))
      (add norm 0 (by grind only [eq_false_intro]))
      (add norm 0 (by grind only [mul_self_eq_mul_self_iff]))
      (add norm 0 (by grind only [Complex.exp_eq_exp_iff_exists_int]))
      (add unsafe 50% (by nlinarith [eq_inv_iff_mul_eq_one]))

  have h8 : t = 3 * (1 : ℝ) + 1 := by
    clear * - h₁ h7
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
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
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by grind only [mul_lt_mul_iff_left]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [FractionalIdeal.dual_eq_mul_inv]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [FractionalIdeal.dual_mul_self]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [FractionalIdeal.dual_dual]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [add_self]))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [AddChar.mulShift_apply]))
      (add norm 0 (by grind only [Pell.d]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [mul_le_mul']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))

  have h9 : t = 4 := by
    clear * - h8
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 256
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
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_self]))
      (add norm 0 (by grind only [Real.Angle.coe_two_pi]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [mul_lt_mul_iff_left]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Fin.val_two]))
      (add norm 0 (by grind only [Ring.multichoose_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [zpow_two]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [Real.norm_two]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add unsafe 90% (by simp only [pow_two] at *))

  have h10 : s = 1 ∧ t = 4 := by
    clear * - h7 h9
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero_z]))
      (add norm 0 (by grind only [one_ne_zero]))
      (add norm 0 (by grind only [False.elim]))
      (add norm 0 (by grind only [and_self]))
      (add norm 0 (by grind only [Pell.Solution₁.ext]))
      (add norm 0 (by rw [Quaternion.coe_one]))
      (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero]))
      (add norm 0 (by grind only [Real.ofCauchy_one]))
      (add norm 0 (by grind only [ArithmeticFunction.one_one]))
      (add norm 0 (by grind only [or_true]))
      (add norm 0 (by grind only [Unitization.snd_one]))
      (add norm 0 (by grind only [eq_false_intro]))
      (add norm 0 (by grind only [rfl]))
      (add norm 0 (by grind only [ArithmeticFunction.intCoe_one]))
      (add norm 0 (by grind only [Real.eq_one_of_pos_of_log_eq_zero]))
      (add norm 0 (by grind only [and_true]))
      (add norm 0 (by grind only [Hyperreal.coe_one]))
      (add norm 0 (by grind only [true_or]))
      (add norm 0 (by grind only [Real.one_rpow]))
      (add norm 0 (by grind only [Hyperreal.Infinitesimal]))
      (add norm 0 (by grind only [Hyperreal.infinitesimal_real_iff]))
      (add norm 0 (by grind only [Hyperreal.coe_eq_coe]))
      (add norm 0 (by grind only [MulChar.one_apply]))
      (add norm 0 (by grind only [UpperHalfPlane.ext_iff]))
      (add norm 0 (by grind only [mul_eq_one]))
      (add norm 0 (by grind only [ArithmeticFunction.natCoe_one]))
      (add norm 0 (by grind only [and_true_iff]))
      (add norm 0 (by grind only [ArithmeticFunction.one_eq_delta]))
      (add unsafe 10% (by grind only [And]))
      (add unsafe 10% (by grind only [Or.elim]))
      (add unsafe 10% (by grind only [Or]))
      (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_lt]))

  exact h10
