import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem imo_1962_p2 (x : ℝ) (h₀ : 0 ≤ 3 - x) (h₁ : 0 ≤ x + 1)
    (h₂ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)) : -1 ≤ x ∧ x < 1 - Real.sqrt 31 / 8 := by
  have h_step_1 : Real.sqrt (3 - x) > Real.sqrt (x + 1) + (1:ℝ) / 2 := by
    clear * - h₂
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 30
      maxGoals := 512
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 100 (by zify))
      (add norm 100 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 1 (by ring_nf))
      (add norm 100 (by ext))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by split))
      (add unsafe 90% (by simp_all))
      (add norm 1 (by simp only [lt_div_iff_mul_lt]))
      (add norm 1 (by simp only [lt_div_iff_mul_lt']))
      (add norm 100 (by rw [div_lt_iff_lt_mul']))
      (add norm 100 (by rw [← div_sub'] at *))
      (add norm 100 (by rw [div_lt_iff_lt_mul]))
      (add norm 1 (by rw [mul_div_cancel_right]))
      (add norm 100 (by rw [Real.log_le_sub_one_of_pos]))
      (add norm 0 (by apply mul_lt_mul_left))
      (add norm 0 (by grind only [Real.div_sqrt]))
      (add norm 0 (by apply mul_lt_mul_right))
      (add norm 100 (by rw [div_le_iff']))
      (add safe 0 (by push_cast [mul_div_cancel_left] at *))
      (add safe 0 (by simp_rw [div_div]))
      (add safe 0 (by simp_all [add_halves]))
      (add safe 1 (by rw [zero_lt_two']))
      (add safe 0 (by simp_all [half_sub]))
      (add unsafe 90% (by rw [← div_lt_iff]))
      (add unsafe 90% (by rw [← lt_div_iff]))
      (add unsafe 10% (by field_simp [one_div] at *))
      (add unsafe 10% (by rw [← sub_half] at *))
      (add unsafe 10% (by push_cast [div_mul] at *))
      (add unsafe 90% (by simp only [one_lt_div']))
      (add unsafe 90% (by simp_rw [Real.rpow_sub]))
      (add unsafe 90% (by rw [← div_lt_iff']))
      (add unsafe 90% (by rw [← lt_div_iff']))
      (add unsafe 90% (by simp_all [sub_div]))
      (add unsafe 90% (by push_cast [inv_div] at *))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul']))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul]))
      (add unsafe 90% (by rw [← inv_pos] at *))
      (add unsafe 90% (by rw [← one_half_pos] at *))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le]))

  have h_step_2 : 3 - x > (Real.sqrt (x + 1) + (1:ℝ) / 2) ^ 2 := by
    clear * - h_step_1 h₀ h₁
    nlinarith [Real.sq_sqrt (show 0 ≤ 3 - x by linarith), Real.sqrt_nonneg (x + 1), Real.sq_sqrt (show 0 ≤ x + 1 by linarith)]

  have h_step_3 : 3 - x > (x + 1) + Real.sqrt (x + 1) + ((1:ℝ) / 4) := by
    clear * - h_step_2
    erw [add_sq] at h_step_2
    simp only [sq, one_div] at h_step_2
    norm_num [mul_add] at *
    by_contra res
    on_goal 1 => revert h_step_2
    intro hp
    refine' res _
    nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt (show 0 ≤ (x + 1) by nlinarith [Real.sqrt_nonneg (x + 1)])]

  have h_step_4 : Real.sqrt (x + 1) < ((7:ℝ) / 4) - 2 * x := by
    clear * - h_step_3
    aesop (config := {
      maxRuleApplications := 700
      maxNormIterations := 30
      maxGoals := 512
      useSimpAll := false
      enableUnfold := false
      useDefaultSimpSet := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 0 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by ext))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 1 (by zify))
      (add safe 0 (by ring_nf))
      (add safe 0 (by split))
      (add safe 0 (by simp_all))
      (add unsafe 90% (by interval_cases))
      (add norm 0 (by apply mul_lt_mul_left))
      (add norm 0 (by apply mul_lt_mul_right))
      (add norm 0 (by rw [← div_lt_div_right]))
      (add norm 100 (by rw [← Real.aux₀] at *))
      (add norm 0 (by simp only [div_sub'] at *))
      (add norm 1 (by simp only [StrictConvexOn.slope_strict_mono_adjacent]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by simp only [div_lt_self_iff] at *))
      (add norm 0 (by grind only [mul_lt_mul_iff_left]))
      (add safe 100 (by positivity [lt_div_iff_mul_lt]))
      (add safe 100 (by positivity [lt_div_iff_mul_lt']))
      (add safe 100 (by positivity [div_lt_iff_lt_mul']))
      (add safe 100 (by positivity [div_lt_iff_lt_mul]))
      (add safe 0 (by simp_all [lt_mul_of_one_lt_left']))
      (add safe 0 (by simp_all [div_mul]))
      (add safe 0 (by simp_all [div_div]))
      (add safe 0 (by simp_all [div_lt_one]))
      (add safe 0 (by simp_all [mul_lt_mul_of_pos_left]))
      (add safe 100 (by simp_all [lt_mul_iff_one_lt_left']))
      (add safe 0 (by simp_all [mul_lt_mul_of_pos_right]))
      (add safe 0 (by simp_all [lt_mul_iff_one_lt_left]))
      (add safe 0 (by simp_all [Real.log_lt_sub_one_of_pos]))
      (add safe 1 (by rw [mul_lt_mul_iff_right]))
      (add safe 1 (by rw [zero_lt_two']))
      (add unsafe 90% (by rw [← div_lt_iff]))
      (add unsafe 90% (by rw [← lt_div_iff]))
      (add unsafe 90% (by rw [← div_lt_iff']))
      (add unsafe 90% (by rw [← lt_div_iff']))
      (add unsafe 10% (by simp only [one_lt_div']))
      (add unsafe 90% (by field_simp [Real.add_lt_add_iff_left] at *))
      (add unsafe 10% (by simp only [Real.pi_div_two_pos]))
      (add unsafe 10% (by simp only [Real.mul_lt_sin]))

  have h_step_5 : ((7:ℝ) / 4) - 2 * x ≥ 0 := by
    clear * - h_step_4 h₁
    linarith [Real.sqrt_nonneg (x + 1), h₁]

  have h_step_6 : x + 1 < (((7:ℝ) / 4) - 2 * x) ^ 2 := by
    clear * - h_step_4 h_step_5
    nth_rewrite 1 [← not_le]
    intro b
    refine h_step_4.not_le (le_of_sub_nonneg ?_)
    nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt (by nlinarith : 0 ≤ x + 1)]

  have h_step_7 : 64 * x ^ 2 - 128 * x + 33 > 0 := by
    clear * - h_step_6
    aesop (config := {
      maxNormIterations := 180
      maxGoals := 32
      useSimpAll := false
      enableUnfold := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by norm_num))
      (add norm 100 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by ext))
      (add norm 0 (by simp))
      (add norm 100 (by field_simp [*] at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by norm_cast))
      (add safe 0 (by abel))
      (add safe 1 (by zify))
      (add safe 0 (by ring_nf))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 0 (by norm_cast at *))
      (add unsafe 90% (by simp_all))
      (add unsafe 90% (by ring_nf at *))
      (add norm 1 (by nlinarith [one_lt_div']))
      (add norm 0 (by rw [← lt_mul_iff_one_lt_left]))
      (add norm 0 (by rw [← mul_lt_iff_lt_one_right]))
      (add norm 1 (by nlinarith [div_lt_self_iff]))
      (add norm 0 (by apply mul_lt_mul_right))
      (add norm 0 (by grind only [zero_lt_two]))
      (add safe 0 (by simp_all [mul_pos_iff_of_pos_left]))
      (add safe 0 (by simp_all [mul_lt_iff_lt_one_left]))
      (add safe 0 (by simp_all [pow_lt_one]))
      (add safe 0 (by nlinarith [div_lt_one]))
      (add safe 100 (by simp [one_lt_sq_iff_one_lt_abs] at *))
      (add safe 0 (by simp_all [lt_mul_of_one_lt_left']))
      (add safe 100 (by simp [lt_mul_iff_one_lt_left'] at *))
      (add safe 0 (by nlinarith [zero_lt_three]))
      (add safe 0 (by nlinarith [Real.aux₀]))
      (add safe 100 (by simp [sq_lt_one_iff] at *))
      (add safe 1 (by grind only [mul_lt_mul_left]))
      (add safe 0 (by nlinarith [zero_lt_one]))
      (add safe 0 (by simp_all [one_half_pos]))
      (add unsafe 10% (by push_cast [sq_pos_of_pos] at *))
      (add unsafe 90% (by grind only [mul_pos_iff_of_pos_right]))
      (add unsafe 10% (by push_cast [Real.sqrt_lt] at *))
      (add unsafe 90% (by grind only [one_lt_div]))
      (add unsafe 10% (by simp only [div_lt_iff']))
      (add unsafe 10% (by simp only [div_lt_iff]))
      (add unsafe 10% (by simp only [Real.pi_gt_three]))
      (add unsafe 90% (by field_simp [lt_mul_iff_one_lt_right'] at *))
      (add unsafe 90% (by rw [← lt_div_iff']))
      (add unsafe 10% (by simp only [lt_div_iff]))
      (add unsafe 10% (by simp only [Real.pi_div_two_pos]))
      (add unsafe 90% (by grind only [Real.mul_pos]))
      (add unsafe 90% (by grind only [EisensteinSeries.r1_pos]))

  have h_step_8 : x < 1 - Real.sqrt 31 / 8 ∨ x > 1 + Real.sqrt 31 / 8 := by
    clear * - h_step_7
    by_cases hx : x < 1 - √31 / 8
    · exact Or.inl hx
    · exact (or_iff_not_imp_left.2 fun h => by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 31)])

  have h_step_9 : x < 1 - Real.sqrt 31 / 8 := by
    clear * - h_step_8 h_step_5
    aesop (config := {
      maxRuleApplications := 700
      maxRuleApplicationDepth := 10
      maxNormIterations := 30
      maxGoals := 512
      useSimpAll := false
      enableUnfold := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 100 (by nlinarith))
      (add norm 100 (by abel))
      (add norm 100 (by push_neg))
      (add norm 100 (by zify))
      (add norm 100 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by decide))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by omega))
      (add safe 0 (by simp_all))
      (add norm 0 (by grind only [mul_lt_mul_left]))
      (add norm 0 (by grind only [mul_lt_mul_right]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 100 (by rw [div_le_iff']))
      (add norm 0 (by grind only [Real.pi_div_two_pos]))
      (add norm 0 (by grind only [div_sub']))
      (add safe 1 (by rw [inv_pos]))
      (add safe 100 (by rw [← lt_mul_of_one_lt_left']))
      (add unsafe 10% (by rw [div_lt_iff]))
      (add unsafe 10% (by rw [lt_div_iff]))
      (add unsafe 10% (by linarith [lt_div_iff_mul_lt]))
      (add unsafe 10% (by rw [div_lt_iff']))
      (add unsafe 10% (by rw [one_lt_div']))
      (add unsafe 10% (by linarith [div_lt_iff_lt_mul']))
      (add unsafe 10% (by linarith [div_lt_iff_lt_mul]))
      (add unsafe 10% (by rw [lt_div_iff']))
      (add unsafe 10% (by linarith [lt_div_iff_mul_lt']))
      (add unsafe 10% (by rw [div_lt_one]))
      (add unsafe 10% (by rw [Real.aux₀]))
      (add unsafe 90% (by push_cast [div_eq_inv_mul] at *))
      (add unsafe 50% (by apply div_le_iff))
      (add unsafe 90% (by grind only [mul_pos_iff_of_pos_left]))
      (add unsafe 90% (by push_cast [inv_div] at *))
      (add unsafe 50% (by apply le_div_iff))
      (add unsafe 10% (by rw [Real.sin_lt]))
      (add unsafe 90% (by grind only [EisensteinSeries.r1_pos]))
      (add unsafe 10% (by rw [Real.mul_lt_sin]))
      (add unsafe 10% (by linarith [Real.add_lt_add_iff_left]))
      (add unsafe 90% (by grind only [one_lt_div]))
      (add unsafe 10% (by linarith [Real.aux₂]))
      (add unsafe 90% (by field_simp [smul_lt_smul_iff_of_pos_left] at *))

  have h_step_10 : -1 ≤ x := by
    clear * - h₁
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 800
      maxGoals := 1024
      enableUnfold := false
      })
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 100 (by abel))
      (add norm 100 (by zify))
      (add norm 0 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 0 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 0 (by decide))
      (add norm 100 (by push_cast))
      (add safe 0 (by omega))
      (add safe 0 (by ring_nf))
      (add safe 0 (by simp_all))
      (add safe 0 (by rfl))
      (add safe 0 (by assumption_mod_cast))
      (add norm 100 (by linarith [one_le_inv_of_le_one]))
      (add norm 100 (by linarith [EReal.le_neg_of_le_neg]))
      (add norm 100 (by linarith [Real.neg_pi_div_two_le_arcsin]))
      (add norm 100 (by linarith [Set.mem_inv]))
      (add norm 100 (by simp_rw [intervalIntegral.integral_neg]))
      (add norm 100 (by simp_rw [neg_eq]))
      (add norm 0 (by grind only [Pi.inv_apply]))
      (add norm 100 (by linarith [SetTheory.PGame.neg_le_iff]))
      (add norm 0 (by grind only [slope_neg]))
      (add norm 100 (by linarith [MeasureTheory.average_neg]))
      (add safe 0 (by rw [← inv_inv]))
      (add safe 0 (by rw [← inv_mabs_le]))
      (add safe 0 (by nlinarith [inv_nonneg]))
      (add unsafe 50% (by simp_rw [inv_le']))
      (add unsafe 50% (by simp_rw [inv_le_inv_iff]))
      (add unsafe 50% (by simp_rw [le_inv']))
      (add unsafe 50% (by simp_rw [Real.log_nonpos]))
      (add unsafe 10% (by simp_all only [EReal.neg_le_neg_iff]))
      (add unsafe 10% (by simp_all only [EReal.neg_le]))
      (add unsafe 10% (by nlinarith [neg_inv]))
      (add unsafe 50% (by simp_rw [leOnePart_eq_inv]))
      (add unsafe 50% (by simp_rw [Real.logb_nonpos]))
      (add unsafe 50% (by simp_rw [leOnePart_eq_one]))
      (add unsafe 90% (by field_simp [inv_neg] at *))
      (add unsafe 50% (by simp_rw [div_nonneg_iff]))
      (add unsafe 50% (by simp_rw [Left.inv_le_one_iff]))
      (add unsafe 50% (by simp_rw [Real.norm_of_nonpos]))
      (add unsafe 50% (by linarith [le_mul_iff_one_le_left']))
      (add unsafe 50% (by simp_rw [Right.inv_le_one_iff]))
      (add unsafe 50% (by simp_rw [one_le_leOnePart]))
      (add unsafe 50% (by simp_rw [Real.exp_le_one_iff]))
      (add unsafe 50% (by linarith [le_mul_iff_one_le_right']))

  exact ⟨h_step_10, h_step_9⟩
