
import Mathlib

open Nat Topology Filter

set_option maxHeartbeats 0

theorem putnam_1967_b2
(p r A B C α β γ : ℝ)
(prbound : 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ r ∧ r ≤ 1)
(id1 : ∀ x y : ℝ, (p * x + (1 - p) * y) ^ 2 = A * x ^ 2 + B * x * y + C * y ^ 2)
(id2 : ∀ x y : ℝ, (p * x + (1 - p) * y) * (r * x + (1 - r) * y) = α * x ^ 2 + β * x * y + γ * y ^ 2)
: max (max A B) C ≥ 4 / 9 ∧ max (max α β) γ ≥ 4 / 9 := by
  have hA : A = p ^ 2 := by
    clear * - id1
    let s1 := id1 1 0
    linear_combination (norm := (ring_nf; linarith)) s1

  have hB : B = 2 * p * (1 - p) := by
    clear * - id1
    linarith [id1 1 1, id1 1 0, id1 (1 / 2) (1 / 2), id1 0 1]

  have hC : C = (1 - p) ^ 2 := by
    clear * - id1
    linarith [id1 0 1, id1 1 1, id1 1 0, id1 (-1) 1]

  have hα : α = p * r := by
    clear * - id2
    linarith [id2 1 0, id2 0 1, id2 1 1, id2 2 0, id2 0 2]

  have hβ : β = p * (1 - r) + r * (1 - p) := by
    clear * - id2
    linarith [id2 1 0, id2 0 1, id2 1 1]

  have hγ : γ = (1 - p) * (1 - r) := by
    clear * - id2
    let s := id2 0 1
    linarith [id2 0 0, id2 0 1, id2 1 1, id2 1 0]

  have hABCSum : A + B + C = 1 := by
    clear * - hA hB hC
    aesop (config := {
      maxRuleApplications := 40
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
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [Pell.Solution₁.prop]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [sq_add_sq_mul_sq_add_sq]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_y]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [CoxeterSystem.IsReflection.pow_two]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [sq_add_mul_sq_mul_sq_add_mul_sq]))
      (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))

  have hαβγSum : α + β + γ = 1 := by
    clear * - hα hβ hγ
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
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_one]))
      (add norm 0 (by grind only [one_mul]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [mul_self]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [FractionalIdeal.dual_eq_mul_inv]))
      (add norm 0 (by grind only [IsLprojection.coe_compl]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [div_mul]))
      (add norm 0 (by grind only [AddChar.one_apply]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [DualNumber.snd_eps]))
      (add norm 0 (by grind only [AddChar.mulShift_apply]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by grind only [mul_inv_cancel]))
      (add norm 0 (by grind only [div_mul_cancel]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [mul_right_inj]))
      (add safe 0 (by simp only [div_self] at *))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))

  have h_max_ABC_def : max (max A B) C = max (max (p ^ 2) (2 * p * (1 - p))) ((1 - p) ^ 2) := by
    clear * - hA hB hC
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableUnfold := false
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
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_max_of_nonneg]))
      (add norm 0 (by grind only [max_eq_left]))
      (add norm 0 (by grind only [max_eq_right]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [max_comm]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Nat.cast_max]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [max_eq_left_iff]))
      (add norm 0 (by grind only [max_one_div_max_inv_one_eq_self]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [max_zero_add_max_neg_zero_eq_abs_self]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Hyperreal.coe_max]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [max_mul_mul_left]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [NNReal.coe_max]))
      (add norm 0 (by grind only [ENNReal.max_zero_right]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [max_ack_right]))
      (add norm 0 (by grind only [max_mul_of_nonneg]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max']))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  have h_min_max_ABC : (∀ p : ℝ, 0 ≤ p → p ≤ 1 → max (max (p ^ 2) (2 * p * (1 - p))) ((1 - p) ^ 2) ≥ 4 / 9) := by
    clear * -
    intro p hp₁ hp₂
    norm_num [max_def, hp₁, hp₂]
    split_ifs <;> nlinarith [sq_nonneg (3 * p - 1), p, 1 - p]

  have hABC_ge : max (max A B) C ≥ 4 / 9 := by
    clear * - h_max_ABC_def h_min_max_ABC prbound
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by rfl))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [max_ack_left]))
      (add norm 0 (by grind only [max_ack_right]))
      (add norm 0 (by grind only [max_eq_right]))
      (add norm 0 (by grind only [max_eq_left]))
      (add norm 0 (by grind only [max_one_div_max_inv_one_eq_self]))
      (add norm 0 (by grind only [max_le_mul_of_one_le]))
      (add norm 0 (by grind only [mul_max_of_nonneg]))
      (add norm 0 (by grind only [max_le_iff]))
      (add norm 0 (by grind only [max_le_max]))
      (add norm 0 (by grind only [ENNReal.max_zero_right]))
      (add norm 0 (by grind only [ENNReal.max_mul]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max']))
      (add norm 0 (by grind only [max_mul_mul_right]))
      (add norm 0 (by grind only [max_mul_of_nonneg]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max_of_aleph0_le_right]))
      (add norm 0 (by grind only [NNReal.coe_max]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max]))
      (add norm 0 (by grind only [Metric.cthickening_max_zero]))
      (add norm 0 (by grind only [tsub_add_eq_max]))
      (add norm 0 (by grind only [max_eq_left_iff]))
      (add norm 0 (by grind only [Valuation.map_add_of_distinct_val]))
      (add norm 0 (by grind only [Cardinal.add_eq_max']))
      (add norm 0 (by grind only [le_max_of_le_right]))
      (add norm 0 (by grind only [ENat.toENNReal_max]))
      (add norm 0 (by grind only [Finset.max_mono]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max_of_aleph0_le_left]))
      (add norm 0 (by grind only [Cardinal.add_eq_max]))
      (add norm 0 (by grind only [Nat.cast_max]))
      (add norm 0 (by grind only [ENNReal.mul_max]))
      (add safe 1 (by simp_all only [max_comm]))
      (add safe 1 (by simp_all only [max_mul_mul_left]))
      (add safe 1 (by simp_all only [max_zero_add_max_neg_zero_eq_abs_self]))

  have h_max_alpha_beta_gamma_def : max (max α β) γ = max (max (p * r) (p * (1 - r) + r * (1 - p))) ((1 - p) * (1 - r)) := by
    clear * - hα hβ hγ
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by rfl))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 0 (by gcongr))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [max_eq_right]))
      (add norm 0 (by grind only [mul_max_of_nonneg]))
      (add norm 0 (by grind only [ENNReal.max_mul]))
      (add norm 0 (by grind only [max_eq_left]))
      (add norm 0 (by grind only [max_ack_right]))
      (add norm 0 (by grind only [max_ack_left]))
      (add norm 0 (by grind only [max_le_iff]))
      (add norm 0 (by grind only [max_mul_of_nonneg]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max']))
      (add norm 0 (by grind only [Valuation.map_add_of_distinct_val]))
      (add norm 0 (by grind only [NNReal.coe_max]))
      (add norm 0 (by grind only [ENNReal.max_zero_right]))
      (add norm 0 (by grind only [max_le_max]))
      (add norm 0 (by grind only [ENNReal.mul_max]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max_of_aleph0_le_right]))
      (add norm 0 (by grind only [tsub_add_eq_max]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max]))
      (add norm 0 (by grind only [Hyperreal.coe_max]))
      (add norm 0 (by grind only [max_eq_left_iff]))
      (add norm 0 (by grind only [ENat.toENNReal_max]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max_of_aleph0_le_left]))
      (add norm 0 (by grind only [Cardinal.add_eq_max']))
      (add norm 0 (by grind only [Metric.cthickening_max_zero]))
      (add norm 0 (by grind only [padicNorm.add_eq_max_of_ne]))
      (add norm 0 (by grind only [padicNorm.nonarchimedean_aux]))
      (add norm 0 (by grind only [Cardinal.add_eq_max]))
      (add norm 0 (by grind only [max_self]))
      (add safe 1 (by simp_all only [max_comm]))
      (add safe 1 (by simp_all only [max_mul_mul_left]))
      (add safe 1 (by simp_all only [max_one_div_max_inv_one_eq_self]))
      (add safe 1 (by simp_all only [max_zero_add_max_neg_zero_eq_abs_self]))
      (add safe 1 (by simp_all only [max_mul_mul_right]))

  have h_min_max_alpha_beta_gamma : (∀ p r : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ r → r ≤ 1 → max (max (p * r) (p * (1 - r) + r * (1 - p))) ((1 - p) * (1 - r)) ≥ 4 / 9) := by
    clear * -
    intro p r hp hr hp' hr'
    norm_num [max_def, hp, hr, hp', hr']
    split_ifs <;> nlinarith [sq_nonneg (r - p), sq_nonneg (r - 1 / 3), sq_nonneg (p - 1 / 3)]

  have hAlphaBetaGamma_ge : max (max α β) γ ≥ 4 / 9 := by
    clear * - h_max_alpha_beta_gamma_def h_min_max_alpha_beta_gamma prbound
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by rfl))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [max_le]))
      (add norm 0 (by grind only [max_le_iff]))
      (add norm 0 (by grind only [max_le_max]))
      (add norm 0 (by grind only [max_ack_left]))
      (add norm 0 (by grind only [le_max_of_le_right]))
      (add norm 0 (by grind only [le_max_of_le_left]))
      (add norm 0 (by grind only [max_le_mul_of_one_le]))
      (add norm 0 (by grind only [max_ack_right]))
      (add norm 0 (by grind only [ENNReal.max_mul]))
      (add norm 0 (by grind only [ENNReal.coe_max]))
      (add norm 0 (by grind only [max_eq_right]))
      (add norm 0 (by grind only [Valuation.map_add]))
      (add norm 0 (by grind only [le_max_right]))
      (add norm 0 (by grind only [max_mul_of_nonneg]))
      (add norm 0 (by grind only [le_max_left]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max]))
      (add norm 0 (by grind only [mul_max_of_nonneg]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max_of_aleph0_le_right]))
      (add norm 0 (by grind only [Max]))
      (add norm 0 (by grind only [NNReal.coe_max]))
      (add norm 0 (by grind only [padicNormE.nonarchimedean]))
      (add norm 0 (by grind only [padicNorm.nonarchimedean_aux]))
      (add norm 0 (by grind only [max_eq_left]))
      (add norm 0 (by grind only [padicNormE.nonarchimedean']))
      (add norm 0 (by grind only [le_max_iff]))
      (add norm 0 (by grind only [ENNReal.mul_max]))
      (add norm 0 (by grind only [PreTilt.valAux_add]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max_of_aleph0_le_left]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max']))
      (add norm 0 (by grind only [max_mul_mul_le_max_mul_max]))
      (add norm 0 (by grind only [Cardinal.add_eq_max]))
      (add safe 1 (by simp_all only [max_comm]))

  have hFinal : max (max A B) C ≥ 4 / 9 ∧ max (max α β) γ ≥ 4 / 9 := by
    clear * - hABC_ge hAlphaBetaGamma_ge
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by rfl))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [max_le_iff]))
      (add norm 0 (by grind only [le_max_of_le_left]))
      (add norm 0 (by grind only [le_max_of_le_right]))
      (add norm 0 (by grind only [max_le]))
      (add norm 0 (by grind only [max_ack_left]))
      (add norm 0 (by grind only [le_max_right]))
      (add norm 0 (by grind only [le_max_left]))
      (add norm 0 (by grind only [Max]))
      (add norm 0 (by grind only [max_le_max]))
      (add norm 0 (by grind only [le_max_iff]))
      (add norm 0 (by grind only [Valuation.map_add]))
      (add norm 0 (by grind only [NNReal.coe_max]))
      (add norm 0 (by grind only [ENNReal.max_mul]))
      (add norm 0 (by grind only [ENNReal.coe_max]))
      (add norm 0 (by grind only [padicNormE.nonarchimedean]))
      (add norm 0 (by grind only [max_eq_right]))
      (add norm 0 (by grind only [AkraBazziRecurrence.max_bi_le]))
      (add norm 0 (by grind only [RightDerivMeasurableAux.A]))
      (add norm 0 (by grind only [Nat.le_max_left]))
      (add norm 0 (by grind only [Nat.le_max_right]))
      (add norm 0 (by grind only [max_ack_right]))
      (add norm 0 (by grind only [padicNorm.nonarchimedean_aux]))
      (add norm 0 (by grind only [max_eq_left]))
      (add norm 0 (by grind only [Cardinal.mul_eq_max]))
      (add norm 0 (by grind only [FDerivMeasurableAux.A]))
      (add norm 0 (by grind only [PreTilt.valAux_add]))
      (add norm 0 (by grind only [padicNormE.nonarchimedean']))
      (add norm 0 (by grind only [RightDerivMeasurableAux.norm_sub_le_of_mem_A]))
      (add norm 0 (by grind only [mul_max_of_nonneg]))
      (add norm 0 (by grind only [FDerivMeasurableAux.A_mono]))
      (add norm 0 (by grind only [PadicInt.nonarchimedean]))
      (add norm 0 (by grind only [Valuation.map_sub]))

  exact hFinal
