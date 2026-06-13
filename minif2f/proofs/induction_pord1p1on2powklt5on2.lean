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
    simp_all only [pow_one, one_div, finite_prod, p_term_1, p_term_2, p_term_3, p_term_4]
    (field_simp)
    (nlinarith)

  let tail_sum := (1 : ℝ) / 16
  have h_tail_sum_val : tail_sum = (1 : ℝ) / 16 := by
    clear * -
    simp_all only [one_div, tail_sum]

  let geo_series_sum := (16 : ℝ) / 15
  have h_geo_series_val : geo_series_sum = (16 : ℝ) / 15 := by
    clear * -
    simp only [geo_series_sum] at *

  let combined_bound := (2295 : ℝ) / 1024 * (16 : ℝ) / 15
  have h_combined_bound_val : combined_bound = (153 : ℝ) / 64 := by
    clear * -
    simp_all only [combined_bound]
    (ring)

  let target_val := (5 : ℝ) / 2
  have h_target_val : target_val = (160 : ℝ) / 64 := by
    clear * -
    simp only [target_val] at *
    (field_simp)
    (ring)

  have h_bound_lt_target : combined_bound < target_val := by
    clear * - h_combined_bound_val h_target_val
    simp_all only [combined_bound, target_val]
    (nlinarith)

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
    simp_all only [Finset.prod_const_one, one_div, combined_bound, target_val]
    (field_simp)
    (field_simp [*] at *)
    (nlinarith)

  exact h_final
