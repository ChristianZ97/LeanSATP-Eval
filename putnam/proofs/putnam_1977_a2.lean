
import Mathlib

set_option maxHeartbeats 0

abbrev putnam_1977_a2_solution : ℝ → ℝ → ℝ → ℝ → Prop := fun a b c d => (a + b = 0 ∧ d = c) ∨ (b + c = 0 ∧ d = a) ∨ (c + a = 0 ∧ d = b)
theorem putnam_1977_a2 :
    ∀ a b c d : ℝ,
      a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
        (putnam_1977_a2_solution a b c d ↔
          (a + b + c = d ∧ 1 / a + 1 / b + 1 / c = 1 / d)) := by
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
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by exfalso))
    (add safe 1 (by ring_nf at *))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 90% (by positivity))
    (add norm 0 (by grind only [inv_ne_zero]))
    (add norm 0 (by grind only [div_ne_one_of_ne]))
    (add norm 0 (by grind only [div_ne_one]))
    (add norm 0 (by grind only [ArithmeticFunction.ext_iff]))
    (add norm 0 (by grind only [inv_ne_one]))
    (add norm 0 (by grind only [FractionalIdeal.dual_ne_zero_iff]))
    (add norm 0 (by grind only [Asymptotics.isTheta_const_const]))
    (add norm 0 (by grind only [Complex.sin_ne_zero_iff]))
    (add norm 0 (by grind only [mul_ne_zero_iff]))
    (add norm 0 (by grind only [Complex.inv_Gammaℝ_two_sub]))
    (add norm 0 (by grind only [iff_def]))
    (add norm 0 (by grind only [div_sub_div]))
    (add norm 0 (by grind only [mul_ne_zero]))
    (add norm 0 (by grind only [div_ne_zero_iff]))
    (add norm 0 (by grind only [map_ne_zero]))
    (add norm 0 (by grind only [WeierstrassCurve.Affine.slope_of_X_ne]))
    (add norm 0 (by grind only [Complex.Gammaℝ_mul_Gammaℝ_add_one]))
    (add norm 0 (by grind only [not_imp_comm]))
    (add norm 0 (by grind only [Complex.Gammaℝ_add_two]))
    (add norm 0 (by grind only [sbtw_mul_sub_add_iff]))
    (add norm 0 (by grind only [irrational_div_rat_iff]))
    (add norm 0 (by grind only [not_imp_not]))
    (add norm 0 (by grind only [inv_sub_inv]))
    (add norm 0 (by grind only [Complex.Gammaℂ_add_one]))
    (add norm 0 (by grind only [forall_and]))
    (add norm 0 (by grind only [WeierstrassCurve.Affine.Nonsingular]))
    (add norm 0 (by grind only [WeierstrassCurve.Affine.nonsingular_iff]))
    (add safe 0 (by simp only [div_ne_zero] at *))
    (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
    (add safe 0 (by simp only [div_self] at *))
    (add safe 0 (by simp only [div_eq_iff] at *))
    (add unsafe 50% (by nlinarith [Real.arctan_ne_mul_pi_div_two]))
