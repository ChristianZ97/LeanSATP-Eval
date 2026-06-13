import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12b_2020_p22 (t : ℝ) : (2 ^ t - 3 * t) * t / 4 ^ t ≤ 1 / 12 := by
  let p2 : ℝ := (2 : ℝ) ^ t
  let p4 : ℝ := (4 : ℝ) ^ t

  have h_pow_eq : p4 = p2 ^ 2 := by
    clear * -
    simp_all only [p4, p2]
    simp [Real.rpow_def_of_pos, p2, p4]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    simp_all only [Nat.cast_ofNat]
    rw [← Real.exp_nat_mul] <;> ring

  have h_num_exp : ((p2 - 3 * t) * t) = t * p2 - 3 * t * t := by
    clear * -
    simp_all only [p2]
    (nlinarith)

  have h_lhs_subst : ((p2 - 3 * t) * t) / p4 = (t * p2 - 3 * t * t) / (p2 ^ 2) := by
    clear * - h_pow_eq h_num_exp
    simp_all only [p4, p2]

  have h_frac_split : (t * p2 - 3 * t * t) / (p2 ^ 2) = (t * p2) / (p2 ^ 2) - (3 * t * t) / (p2 ^ 2) := by
    clear * -
    simp_all only [p2]
    (field_simp)

  have h_term1_simp : (t * p2) / (p2 ^ 2) = t / p2 := by
    clear * -
    simp_all only [p2]
    (field_simp)
    (nlinarith)

  have h_term2_simp : (3 * t * t) / (p2 ^ 2) = 3 * (t / p2) ^ 2 := by
    clear * -
    simp_all only [p2]
    (field_simp)
    (nlinarith)

  have h_lhs_u_form : ((p2 - 3 * t) * t) / p4 = t / p2 - 3 * (t / p2) ^ 2 := by
    clear * - h_lhs_subst h_frac_split h_term1_simp h_term2_simp
    simp_all only [p2, p4]

  let u : ℝ := t / p2

  have h_lhs_u : ((p2 - 3 * t) * t) / p4 = u - 3 * u ^ 2 := by
    clear * - h_lhs_u_form
    simp_all only [p2, p4, u]

  have h_quad_id : u - 3 * u ^ 2 = -3 * (u - 1 / 6) ^ 2 + 1 / 12 := by
    clear * -
    simp_all only [one_div, neg_mul, u, p2]
    (field_simp)
    (nlinarith)

  have h_sq_nonneg : (u - 1 / 6) ^ 2 ≥ 0 := by
    clear * -
    simp_all only [one_div, ge_iff_le, u, p2]
    (field_simp)
    (bound )

  have h_neg_sq_nonpos : -3 * (u - 1 / 6) ^ 2 ≤ 0 := by
    clear * - h_sq_nonneg
    simp_all only [one_div, ge_iff_le, neg_mul, Left.neg_nonpos_iff, ofNat_pos, mul_nonneg_iff_of_pos_left, u, p2]

  have h_final_ineq : -3 * (u - 1 / 6) ^ 2 + 1 / 12 ≤ 1 / 12 := by
    clear * - h_neg_sq_nonpos
    simp_all only [one_div, neg_mul, Left.neg_nonpos_iff, ofNat_pos, mul_nonneg_iff_of_pos_left, add_le_iff_nonpos_left, u,
    p2]

  have h_main_result : ((p2 - 3 * t) * t) / p4 ≤ 1 / 12 := by
    clear * - h_lhs_u h_quad_id h_final_ineq
    simp_all only [one_div, neg_mul, add_le_iff_nonpos_left, Left.neg_nonpos_iff, ofNat_pos, mul_nonneg_iff_of_pos_left, p2,
    p4, u]

  have h_conclusion : (2 ^ t - 3 * t) * t / 4 ^ t ≤ 1 / 12 := by
    clear * - h_main_result
    simp_all only [one_div, p2, p4]

  exact h_conclusion