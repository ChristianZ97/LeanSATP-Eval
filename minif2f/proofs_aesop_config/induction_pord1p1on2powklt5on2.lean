import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem induction_pord1p1on2powklt5on2 (n : ℕ) (h₀ : 0 < n) :
    (∏ k in Finset.Icc 1 n, 1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := by
  let prod_1_to_4 := (1 : ℝ) + (1 : ℝ) / 2 ^ 1 * (1 : ℝ) + (1 : ℝ) / 2 ^ 2 * (1 : ℝ) + (1 : ℝ) / 2 ^ 3 * (1 : ℝ) + (1 : ℝ) / 2 ^ 4
  let p_term_1 := 1 + (1 : ℝ) / (2 : ℝ) ^ 1
  let p_term_2 := 1 + (1 : ℝ) / (2 : ℝ) ^ 2
  let p_term_3 := 1 + (1 : ℝ) / (2 : ℝ) ^ 3
  let p_term_4 := 1 + (1 : ℝ) / (2 : ℝ) ^ 4
  let finite_prod := p_term_1 * p_term_2 * p_term_3 * p_term_4

  have h_finite_prod_val : finite_prod = (2295 : ℝ) / 1024 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_inv_app | rw [CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_inv_app] | simp only [CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_inv_app]))
    (add unsafe 30% (by first | apply FiberBundle.extChartAt_target | rw [FiberBundle.extChartAt_target] | simp only [FiberBundle.extChartAt_target]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd | rw [Ordinal.nadd_lt_nadd] | simp only [Ordinal.nadd_lt_nadd]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_le_of_lt | rw [Ordinal.nadd_lt_nadd_of_le_of_lt] | simp only [Ordinal.nadd_lt_nadd_of_le_of_lt]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_lt_of_le | rw [Ordinal.nadd_lt_nadd_of_lt_of_le] | simp only [Ordinal.nadd_lt_nadd_of_lt_of_le]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_right | rw [Ordinal.nadd_lt_nadd_right] | simp only [Ordinal.nadd_lt_nadd_right]))

  let tail_sum := (1 : ℝ) / 16
  have h_tail_sum_val : tail_sum = (1 : ℝ) / 16 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply one_div | rw [one_div] | simp only [one_div]))
    (add unsafe 10% (by first | apply Complex.ofReal_inv | rw [Complex.ofReal_inv] | simp only [Complex.ofReal_inv]))
    (add unsafe 10% (by first | apply Quaternion.coe_one | rw [Quaternion.coe_one] | simp only [Quaternion.coe_one]))
    (add unsafe 10% (by first | apply inv_eq_one_div | rw [inv_eq_one_div] | simp only [inv_eq_one_div]))
    (add unsafe 10% (by first | apply mul_inv_cancel | rw [mul_inv_cancel] | simp only [mul_inv_cancel]))

  let geo_series_sum := (16 : ℝ) / 15
  have h_geo_series_val : geo_series_sum = (16 : ℝ) / 15 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    useSimpAll              := false
    })
    (add safe 2 (by field_simp))
    (add safe 2 (by ring))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply inv_eq_one_div | rw [inv_eq_one_div] | simp only [inv_eq_one_div]))
    (add unsafe 30% (by first | apply one_div | rw [one_div] | simp only [one_div]))
    (add unsafe 10% (by first | apply div_self | rw [div_self] | simp only [div_self]))
    (add unsafe 10% (by first | apply integral_one_div_of_pos | rw [integral_one_div_of_pos] | simp only [integral_one_div_of_pos]))
    (add unsafe 10% (by first | apply mul_one_div | rw [mul_one_div] | simp only [mul_one_div]))
    (add unsafe 10% (by first | apply one_div_one | rw [one_div_one] | simp only [one_div_one]))

  let combined_bound := (2295 : ℝ) / 1024 * (16 : ℝ) / 15
  have h_combined_bound_val : combined_bound = (153 : ℝ) / 64 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 10% (by first | apply div_self | rw [div_self] | simp only [div_self]))

  let target_val := (5 : ℝ) / 2
  have h_target_val : target_val = (160 : ℝ) / 64 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    useSimpAll              := false
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add safe 4 (by ring))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply div_le_div_left | rw [div_le_div_left] | simp only [div_le_div_left]))
    (add unsafe 30% (by first | apply div_le_iff' | rw [div_le_iff'] | simp only [div_le_iff']))
    (add unsafe 30% (by first | apply zero_lt_two' | rw [zero_lt_two'] | simp only [zero_lt_two']))
    (add unsafe 10% (by first | apply Behrend.ceil_lt_mul | rw [Behrend.ceil_lt_mul] | simp only [Behrend.ceil_lt_mul]))
    (add unsafe 10% (by first | apply div_le_div_right | rw [div_le_div_right] | simp only [div_le_div_right]))
    (add unsafe 10% (by first | apply div_le_iff | rw [div_le_iff] | simp only [div_le_iff]))
    (add unsafe 10% (by first | apply le_div_iff' | rw [le_div_iff'] | simp only [le_div_iff']))

  have h_bound_lt_target : combined_bound < target_val := by
    clear * - h_combined_bound_val h_target_val
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_Sn_lt_bound : (∏ k in Finset.Icc 1 n, 1 + (1 : ℝ) / 2 ^ k) < combined_bound := by
    clear * - h_finite_prod_val h_tail_sum_val h_geo_series_val
    simp_all only [pow_one, one_div, Finset.prod_const_one, finite_prod, p_term_1, p_term_2, p_term_3, p_term_4, tail_sum,
      geo_series_sum, combined_bound]
    field_simp
    rw [div_lt_div_iff] <;> norm_num1
    · ring_nf
      induction k <;> simp [pow_succ] <;> linarith
    · simp_all only [ofNat_pos, pow_pos]

  have h_final : (∏ k in Finset.Icc 1 n, 1 + (1 : ℝ) / 2 ^ k) < (5 : ℝ) / 2 := by
    clear * - h_Sn_lt_bound h_bound_lt_target
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  exact h_final
