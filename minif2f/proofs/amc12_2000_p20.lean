import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12_2000_p20 (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x + 1 / y = 4)
    (h₂ : y + 1 / z = 1) (h₃ : z + 1 / x = 7 / 3) : x * y * z = 1 := by
  have h_pos_prod : 0 < x * y * z := by
    clear * - h₀
    simp_all only [mul_pos_iff_of_pos_left]

  have h_prod_eq : (x + (1 : ℝ) / y) * (y + (1 : ℝ) / z) * (z + (1 : ℝ) / x) = (4 : ℝ) * (1 : ℝ) * ((7 : ℝ) / 3) := by
    clear * - h₁ h₂ h₃
    simp_all only [one_div, mul_one]

  have h_rhs_calc : (4 : ℝ) * (1 : ℝ) * ((7 : ℝ) / 3) = (28 : ℝ) / 3 := by
    clear * -
    simp_all only [mul_one]
    (field_simp)
    (ring)

  have h_combined_prod : (x + (1 : ℝ) / y) * (y + (1 : ℝ) / z) * (z + (1 : ℝ) / x) = (28 : ℝ) / 3 := by
    clear * - h_prod_eq h_rhs_calc
    simp_all only [one_div, mul_one]

  have h_lhs_expand : (x + (1 : ℝ) / y) * (y + (1 : ℝ) / z) * (z + (1 : ℝ) / x) =
      x * y * z + (x + (1 : ℝ) / y) + (y + (1 : ℝ) / z) + (z + (1 : ℝ) / x) + (1 : ℝ) / (x * y * z) := by
    clear * - h₀
    simp_all only [one_div, mul_inv_rev]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    (field_simp)
    (nlinarith)

  have h_substituted_vals : x * y * z + (4 : ℝ) + (1 : ℝ) + ((7 : ℝ) / 3) + (1 : ℝ) / (x * y * z) = (28 : ℝ) / 3 := by
    clear * - h_combined_prod h_lhs_expand h₁ h₂ h₃
    simp_all only [one_div, mul_one, mul_inv_rev]

  have h_int_sum : (4 : ℝ) + (1 : ℝ) = (5 : ℝ) := by
    clear * -
    (ring)

  have h_total_const : (5 : ℝ) + ((7 : ℝ) / 3) = (22 : ℝ) / 3 := by
    clear * - h_int_sum
    aesop
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add unsafe 100% (by nlinarith))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by bound))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_num [*] at *))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 40% (by first | apply div_ne_one | rw [div_ne_one] | simp only [div_ne_one]))
    (add unsafe 30% (by first | apply Int.cast_lt | rw [Int.cast_lt] | simp only [Int.cast_lt]))
    (add unsafe 30% (by first | apply Real.arctan_ne_mul_pi_div_two | rw [Real.arctan_ne_mul_pi_div_two] | simp only [Real.arctan_ne_mul_pi_div_two]))
    (add unsafe 30% (by first | apply div_lt_iff_lt_mul | rw [div_lt_iff_lt_mul] | simp only [div_lt_iff_lt_mul]))
    (add unsafe 30% (by first | apply div_ne_one_of_ne | rw [div_ne_one_of_ne] | simp only [div_ne_one_of_ne]))
    (add unsafe 30% (by first | apply mabs_lt | rw [mabs_lt] | simp only [mabs_lt]))

  have h_reduced_eq : x * y * z + ((22 : ℝ) / 3) + (1 : ℝ) / (x * y * z) = (28 : ℝ) / 3 := by
    clear * - h_substituted_vals h_total_const
    simp_all only [one_div, mul_inv_rev]
    (field_simp)
    (field_simp [*] at *)
    (nlinarith)

  have h_isolate_var_term : x * y * z + (1 : ℝ) / (x * y * z) = (28 : ℝ) / 3 - (22 : ℝ) / 3 := by
    clear * - h_reduced_eq
    simp_all only [one_div, mul_inv_rev]
    linear_combination h_reduced_eq

  have h_diff_calc : (28 : ℝ) / 3 - (22 : ℝ) / 3 = (6 : ℝ) / 3 := by
    clear * -
    (field_simp)
    (ring)

  have h_frac_simp : (6 : ℝ) / 3 = (2 : ℝ) := by
    clear * -
    (field_simp)
    (ring)

  have h_recip_relation : x * y * z + (1 : ℝ) / (x * y * z) = (2 : ℝ) := by
    clear * - h_isolate_var_term h_diff_calc h_frac_simp
    simp_all only [one_div, mul_inv_rev]

  have h_no_denom : (x * y * z) * (x * y * z) + (1 : ℝ) = (2 : ℝ) * (x * y * z) := by
    clear * - h_recip_relation h_pos_prod
    simp_all only [one_div, mul_inv_rev]
    (field_simp [*] at *)
    simp_all only [one_div, mul_inv_rev]
    (field_simp [*] at *)
    simp_all only

  have h_quadratic_form : (x * y * z) * (x * y * z) - (2 : ℝ) * (x * y * z) + (1 : ℝ) = (0 : ℝ) := by
    clear * - h_no_denom
    (nlinarith)

  have h_perfect_square : ((x * y * z) - (1 : ℝ)) ^ 2 = (0 : ℝ) := by
    clear * - h_quadratic_form
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    (nlinarith)

  have h_zero_base : (x * y * z) - (1 : ℝ) = (0 : ℝ) := by
    clear * - h_perfect_square
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]

  have h_final_result : x * y * z = (1 : ℝ) := by
    clear * - h_zero_base
    (nlinarith)

  exact h_final_result
