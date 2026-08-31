
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

theorem algebra_bleqa_apbon2msqrtableqambsqon8b (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : b ≤ a) :
    (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  have ha_pos : 0 < a := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 0 (by gcongr))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [lt_trichotomy]))
      (add norm 0 (by grind only [EisensteinSeries.r]))
      (add norm 0 (by grind only [mul_neg_of_neg_of_pos]))
      (add norm 0 (by grind only [lt_sup_iff]))
      (add norm 0 (by grind only [Real.sign]))
      (add unsafe 50% (by nlinarith [Real.mul_pos]))
      (add unsafe 50% (by nlinarith [zero_lt_one]))
      (add unsafe 50% (by nlinarith [Real.b_pos]))
      (add unsafe 50% (by nlinarith [inv_pos]))
      (add unsafe 50% (by nlinarith [Real.rpow_pos_of_pos]))
      (add unsafe 50% (by nlinarith [Real.log_neg]))
      (add unsafe 50% (by nlinarith [one_lt_gold]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r1_pos]))
      (add unsafe 50% (by nlinarith [mul_pos_iff]))
      (add unsafe 50% (by nlinarith [Real.rpow_lt_rpow]))
      (add unsafe 50% (by nlinarith [lt_inv]))
      (add unsafe 50% (by nlinarith [Real.rpow_logb]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_one_iff]))
      (add unsafe 50% (by nlinarith [inv_lt_one]))
      (add unsafe 50% (by nlinarith [Real.arcsin_pos]))
      (add unsafe 50% (by nlinarith [Real.log_pos]))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [inv_lt]))
      (add unsafe 50% (by nlinarith [Real.logb_neg]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [Real.sin_pos_of_pos_of_lt_pi]))
      (add unsafe 50% (by nlinarith [pow_lt_one]))
      (add unsafe 50% (by nlinarith [one_half_lt_one]))
      (add unsafe 50% (by nlinarith [Real.logb_pos]))
      (add unsafe 50% (by nlinarith [one_half_pos]))
      (add unsafe 50% (by nlinarith [div_pos]))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_right]))

  have hb_pos : 0 < b := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_neg_of_neg_of_pos]))
      (add norm 0 (by grind only [lt_trichotomy]))
      (add norm 0 (by grind only [EisensteinSeries.r]))
      (add norm 0 (by grind only [lt_sup_iff]))
      (add unsafe 50% (by nlinarith [Real.mul_pos]))
      (add unsafe 50% (by nlinarith [Real.b_pos]))
      (add unsafe 50% (by nlinarith [zero_lt_one]))
      (add unsafe 50% (by nlinarith [Real.rpow_pos_of_pos]))
      (add unsafe 50% (by nlinarith [inv_pos]))
      (add unsafe 50% (by nlinarith [Real.log_neg]))
      (add unsafe 50% (by nlinarith [Real.rpow_lt_rpow]))
      (add unsafe 50% (by nlinarith [Real.rpow_logb]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r1_pos]))
      (add unsafe 50% (by nlinarith [lt_inv]))
      (add unsafe 50% (by nlinarith [one_lt_gold]))
      (add unsafe 50% (by nlinarith [mul_pos_iff]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_one_iff]))
      (add unsafe 50% (by nlinarith [Real.log_pos]))
      (add unsafe 50% (by nlinarith [inv_lt_one]))
      (add unsafe 50% (by nlinarith [inv_lt]))
      (add unsafe 50% (by nlinarith [Real.logb_neg]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [Real.arcsin_pos]))
      (add unsafe 50% (by nlinarith [pow_lt_one]))
      (add unsafe 50% (by nlinarith [Real.rpow_lt_rpow_of_exponent_gt]))
      (add unsafe 50% (by nlinarith [Real.sign]))
      (add unsafe 50% (by nlinarith [Real.sin_pos_of_pos_of_lt_pi]))
      (add unsafe 50% (by nlinarith [Real.logb_pos]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [one_half_lt_one]))
      (add unsafe 50% (by nlinarith [inv_lt_inv]))

  -- Step 1: sqrt(b) <= sqrt(a)
  have h_sqrt_b_le_sqrt_a : Real.sqrt b ≤ Real.sqrt a := by
    clear * - h₁ ha_pos hb_pos
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 520
      enableUnfold := false
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
      (add norm 0 (by grind only [Real.sqrt_le_sqrt_iff]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [smul_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt_iff']))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [Real.sqrtTwoAddSeries_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.rpow_le_rpow]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Real.abs_le_sqrt]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [Bertrand.real_main_inequality]))
      (add norm 0 (by grind only [Real.rpow_nonneg]))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [mul_self_nonneg]))
      (add norm 0 (by grind only [Complex.abs_le_sqrt_two_mul_max]))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [EisensteinSeries.auxbound2]))
      (add norm 0 (by grind only [Real.sqrt_le_iff]))

  -- Step 2: sqrt(a) + sqrt(b) >= 2*sqrt(b)
  have h_sum_sqrt_ge_2sqrt_b : Real.sqrt a + Real.sqrt b ≥ 2 * Real.sqrt b := by
    clear * - h_sqrt_b_le_sqrt_a hb_pos
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by rw [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [le_mul_left]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [mul_add_mul_le_mul_add_mul]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Finset.sum_condensed_le]))
      (add norm 0 (by grind only [le_mul_right]))
      (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Valuation.map_add_le]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [Real.BohrMollerup.f_add_nat_ge]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [AkraBazziRecurrence.one_add_smoothingFn_le_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [self_le_mul_left]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [le_self_mul]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [Finset.le_sum_condensed]))
      (add norm 0 (by grind only [self_le_mul_right]))

  -- Step 3: (sqrt(a) + sqrt(b))^2 >= 4*b
  have h_sq_sum_sqrt_ge_4b : (Real.sqrt a + Real.sqrt b) ^ 2 ≥ 4 * b := by
    clear * - h_sum_sqrt_ge_2sqrt_b hb_pos
    rw [mul_comm 2 _] at h_sum_sqrt_ge_2sqrt_b
    rw [pow_two]
    have h2 : 0 ≤ (√a - √b) ^ 2 := sq_nonneg (√a - √b)
    nlinarith [Real.sq_sqrt hb_pos.le, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

  -- Step 4: (sqrt(a) + sqrt(b))^2 / (8*b) >= 1/2
  have h_frac_sq_sum_ge_half : (Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b) ≥ (1:ℝ) / 2 := by
    clear * - h_sq_sum_sqrt_ge_4b hb_pos
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [div_le_div_right]))
      (add norm 0 (by grind only [Real.pi_le_four]))
      (add norm 0 (by grind only [div_le_div_left]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [div_pow_le]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [div_le_self]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
      (add norm 0 (by grind only [Bertrand.real_main_inequality]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [SzemerediRegularity.hundred_div_ε_pow_five_le_m]))
      (add norm 0 (by grind only [NumberField.abs_discr_ge]))
      (add norm 0 (by grind only [SzemerediRegularity.pow_mul_m_le_card_part]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [SzemerediRegularity.hundred_le_m]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold div_le_one))
      (add safe 1 (by unfold one_le_div))
      (add safe 1 (by unfold div_le_div_iff))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))

  -- Step 5: ((sqrt(a) - sqrt(b))^2 * (sqrt(a) + sqrt(b))^2) / (8*b) >= (sqrt(a) - sqrt(b))^2 / 2
  -- Note: (sqrt(a) - sqrt(b))^2 is non-negative, so we can multiply both sides of Step 4 by it.
  let sq_diff_sqrt := (Real.sqrt a - Real.sqrt b) ^ 2
  have h_nonneg_sq_diff : 0 ≤ sq_diff_sqrt := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [mul_self_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt_iff]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_coe_center_sq]))
      (add norm 0 (by grind only [EisensteinSeries.auxbound2]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [EisensteinSeries.auxbound1]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  have h_frac_term_ge_half_sq_diff : (sq_diff_sqrt * (Real.sqrt a + Real.sqrt b) ^ 2) / (8 * b) ≥ sq_diff_sqrt / 2 := by
    clear * - h_frac_sq_sum_ge_half h_nonneg_sq_diff hb_pos
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [mul_le_mul_right]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Real.pi_le_four]))
      (add norm 0 (by grind only [div_le_div_right]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [div_pow_le]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [div_le_div]))
      (add norm 0 (by grind only [div_le_self]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [Bertrand.real_main_inequality]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [SzemerediRegularity.pow_mul_m_le_card_part]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_right]))
      (add norm 0 (by grind only [mul_le_of_le_one_left]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold div_le_one))
      (add safe 1 (by unfold one_le_div))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))

  -- Step 6: (a - b)^2 / (8*b) >= (a + b - 2*sqrt(ab)) / 2
  -- Note: (sqrt(a) - sqrt(b))^2 * (sqrt(a) + sqrt(b))^2 = (a - b)^2
  -- And (sqrt(a) - sqrt(b))^2 = a + b - 2*sqrt(a*b)
  have h_identity_num : (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 = (a - b) ^ 2 := by
    clear * - ha_pos hb_pos
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 60
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [Real.rpow_two]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [norm_add_sq_real]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [norm_add_sq]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [integral_gaussian]))
      (add norm 0 (by grind only [EuclideanSpace.dist_eq]))
      (add norm 0 (by grind only [norm_sub_sq_real]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [PiLp.norm_eq_of_L2]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [WithLp.prod_norm_sq_eq_of_L2]))
      (add norm 0 (by grind only [norm_sub_sq]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [abs_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  have h_identity_denom_part : (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * Real.sqrt (a * b) := by
    clear * - ha_pos hb_pos
    ring <;> simp [sq, mul_add, add_mul]
    repeat' rw [Real.sqrt_mul (by positivity)]; ring
    simpa [Real.sq_sqrt ha_pos.le, Real.sq_sqrt hb_pos.le] using mul_pos ha_pos hb_pos

  have h_final_rhs_eq : (a + b - 2 * Real.sqrt (a * b)) / 2 = (a + b) / 2 - Real.sqrt (a * b) := by
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
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.cos_sq]))
      (add norm 0 (by grind only [div_add_div_same]))
      (add norm 0 (by grind only [add_self_div_two]))
      (add norm 0 (by grind only [mul_div_right_comm]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [goldenConj]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [aux_add]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Real.cos_half]))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 1 (by apply div_mul))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [div_right_comm] at *))

  -- Combine everything
  have h_main_ineq : (a - b) ^ 2 / (8 * b) ≥ (a + b - 2 * Real.sqrt (a * b)) / 2 := by
    clear * - h_frac_term_ge_half_sq_diff h_identity_num h_identity_denom_part hb_pos
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [mul_le_mul_right]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [div_le_div_right]))
      (add norm 0 (by grind only [one_le_div]))
      (add norm 0 (by grind only [Real.pi_le_four]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [div_le_self]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [div_le_div_left]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [div_pow_le]))
      (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
      (add norm 0 (by grind only [Behrend.ceil_lt_mul]))
      (add norm 0 (by grind only [mul_div_assoc']))
      (add norm 0 (by grind only [SzemerediRegularity.hundred_div_ε_pow_five_le_m]))
      (add norm 0 (by grind only [SzemerediRegularity.pow_mul_m_le_card_part]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [Bertrand.real_main_inequality]))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold div_le_one))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div] at *))

  have h_final_form : (a - b) ^ 2 / (8 * b) ≥ (a + b) / 2 - Real.sqrt (a * b) := by
    clear * - h_main_ineq h_final_rhs_eq
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 520
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [le_div_iff]))
      (add norm 0 (by grind only [div_le_iff']))
      (add norm 0 (by grind only [div_le_iff]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [mul_le_mul_right]))
      (add norm 0 (by grind only [div_le_div_right]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [div_le_div_iff]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [mul_div_assoc']))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [Bertrand.real_main_inequality]))
      (add norm 0 (by grind only [mul_div_right_comm]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [div_mul] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 1 (by unfold div_le_one))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add unsafe 50% (by simp only [sq_sub_sq]))

  exact h_final_form
