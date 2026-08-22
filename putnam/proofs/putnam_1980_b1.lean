
import Mathlib

open Real

set_option maxHeartbeats 0

abbrev putnam_1980_b1_solution : Set ℝ := {c | ∀ x : ℝ, (exp x + exp (-x)) / 2 ≤ exp (c * x ^ 2)}
theorem putnam_1980_b1
(c : ℝ)
: (∀ x : ℝ, (exp x + exp (-x)) / 2 ≤ exp (c * x ^ 2)) ↔ c ∈ putnam_1980_b1_solution := by
  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Real.exp_le_exp]))
    (add norm 0 (by grind only [Real.exp_pos]))
    (add norm 0 (by grind only [Real.exp_eq_exp_ℝ]))
    (add norm 0 (by grind only [Real.le_log_iff_exp_le]))
    (add norm 0 (by grind only [Real.exp_sub]))
    (add norm 0 (by grind only [Real.exp_mul]))
    (add norm 0 (by grind only [Real.exp]))
    (add norm 0 (by grind only [Real.exp_ne_zero]))
    (add norm 0 (by grind only [Real.exp_add]))
    (add norm 0 (by grind only [rexp_neg_deriv_aux]))
    (add norm 0 (by grind only [rexp_neg_injOn_aux]))
    (add norm 0 (by grind only [Real.exp_log]))
    (add norm 0 (by grind only [Real.exp_nonneg]))
    (add norm 0 (by grind only [Real.log_exp]))
    (add norm 0 (by grind only [Real.log_le_iff_le_exp]))
    (add norm 0 (by grind only [Real.exp_arsinh]))
    (add norm 0 (by grind only [integral_exp]))
    (add norm 0 (by grind only [Real.exp_half]))
    (add norm 0 (by grind only [Real.exp_nat_mul]))
    (add norm 0 (by grind only [Real.exp_one_rpow]))
    (add norm 0 (by grind only [Real.add_one_le_exp]))
    (add norm 0 (by grind only [rexp_neg_image_aux]))
    (add norm 0 (by grind only [Real.exp_injective]))
    (add norm 0 (by grind only [Real.measurable_exp]))
    (add norm 0 (by grind only [MeasureTheory.integral_exp_pos]))
    (add norm 0 (by grind only [ProbabilityTheory.measure_ge_le_exp_mul_mgf]))
    (add norm 0 (by grind only [Real.rpow_def_of_pos]))
    (add norm 0 (by grind only [ProbabilityTheory.measure_le_le_exp_mul_mgf]))
    (add norm 0 (by grind only [Real.le_exp_log]))
    (add norm 0 (by grind only [HurwitzKernelBounds.exp_lt_aux]))
    (add norm 0 (by grind only [Real.exp_log_eq_abs]))
    (add unsafe 50% (by nlinarith [Behrend.exp_neg_two_mul_le]))
