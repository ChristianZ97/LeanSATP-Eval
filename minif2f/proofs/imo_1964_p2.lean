import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have h_diff_poly :
    3 * a * b * c - (a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c)) =
    a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c - (a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2) := by
    clear * -
    (nlinarith)

  have h_poly_fact :
    a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c - (a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2) =
    a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) := by
    clear * -
    (nlinarith)

  have h_fact_sos :
    a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) =
    (1:ℝ) / 2 * ((a + b - c) * (a - b) ^ 2 + (b + c - a) * (b - c) ^ 2 + (c + a - b) * (c - a) ^ 2) := by
    clear * -
    simp_all only [one_div]
    (field_simp)
    (nlinarith)

  have h_diff_sos :
    3 * a * b * c - (a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c)) =
    (1:ℝ) / 2 * ((a + b - c) * (a - b) ^ 2 + (b + c - a) * (b - c) ^ 2 + (c + a - b) * (c - a) ^ 2) := by
    clear * - h_diff_poly h_poly_fact h_fact_sos
    simp_all only [one_div]

  have h_t1_coeff_pos : 0 < a + b - c := by
    clear * - h₁
    simp_all only [sub_pos]

  have h_t1_sq_nonneg : 0 ≤ (a - b) ^ 2 := by
    clear * -
    (nlinarith)

  have h_t1_nonneg : (1:ℝ) / 2 * (a + b - c) * (a - b) ^ 2 ≥ 0 := by
    clear * - h_t1_coeff_pos h_t1_sq_nonneg
    simp_all only [sub_pos, one_div, ge_iff_le, inv_pos, ofNat_pos, mul_pos_iff_of_pos_left, mul_nonneg_iff_of_pos_left]

  have h_t2_coeff_pos : 0 < b + c - a := by
    clear * - h₃
    simp_all only [sub_pos]

  have h_t2_sq_nonneg : 0 ≤ (b - c) ^ 2 := by
    clear * -
    (nlinarith)

  have h_t2_nonneg : (1:ℝ) / 2 * (b + c - a) * (b - c) ^ 2 ≥ 0 := by
    clear * - h_t2_coeff_pos h_t2_sq_nonneg
    simp_all only [sub_pos, one_div, ge_iff_le, inv_pos, ofNat_pos, mul_pos_iff_of_pos_left, mul_nonneg_iff_of_pos_left]

  have h_t3_coeff_pos : 0 < c + a - b := by
    clear * - h₂
    simp_all only [sub_pos]
    (nlinarith)

  have h_t3_sq_nonneg : 0 ≤ (c - a) ^ 2 := by
    clear * -
    (nlinarith)

  have h_t3_nonneg : (1:ℝ) / 2 * (c + a - b) * (c - a) ^ 2 ≥ 0 := by
    clear * - h_t3_coeff_pos h_t3_sq_nonneg
    simp_all only [sub_pos, one_div, ge_iff_le, inv_pos, ofNat_pos, mul_pos_iff_of_pos_left, mul_nonneg_iff_of_pos_left]

  have h_sos_sum_nonneg :
    (1:ℝ) / 2 * ((a + b - c) * (a - b) ^ 2 + (b + c - a) * (b - c) ^ 2 + (c + a - b) * (c - a) ^ 2) ≥ 0 := by
    clear * - h_t1_nonneg h_t2_nonneg h_t3_nonneg
    simp_all only [one_div, ge_iff_le, inv_pos, ofNat_pos, mul_nonneg_iff_of_pos_left]
    (nlinarith)

  have h_D_ge_zero :
    3 * a * b * c - (a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c)) ≥ 0 := by
    clear * - h_diff_sos h_sos_sum_nonneg
    simp_all only [one_div, ge_iff_le, inv_pos, ofNat_pos, mul_nonneg_iff_of_pos_left]

  linarith