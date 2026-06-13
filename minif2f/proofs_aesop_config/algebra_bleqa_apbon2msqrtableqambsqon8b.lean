import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem algebra_bleqa_apbon2msqrtableqambsqon8b (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : b ≤ a) :
    (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  have ha : 0 < a := h₀.1
  have hb : 0 < b := h₀.2

  have h_step1 : (a + b) / (2 : ℝ) - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b) ^ 2 / (2 : ℝ) := by
    clear * - ha hb
    (field_simp)
    (ring_nf at *)
    (field_simp)
    (nlinarith)

  have h_step2_diff : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
    clear * - ha hb
    (ring_nf at *)
    (field_simp)

  have h_step2_sqr : (a - b) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    clear * - h_step2_diff
    simp_all only
    (nlinarith)

  have h_step2 : (a - b) ^ 2 / ((8 : ℝ) * b) = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 / ((8 : ℝ) * b) := by
    clear * - h_step2_sqr hb
    simp_all only

  let delta : ℝ := (a - b) ^ 2 / ((8 : ℝ) * b) - ((a + b) / (2 : ℝ) - Real.sqrt (a * b))

  have h_step4 : delta = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 / ((8 : ℝ) * b) - (Real.sqrt a - Real.sqrt b) ^ 2 / (2 : ℝ) := by
    clear * - h_step1 h_step2
    simp_all only [delta]

  have h_step5 : delta = (Real.sqrt a - Real.sqrt b) ^ 2 / (2 : ℝ) * (((Real.sqrt a + Real.sqrt b) ^ 2) / ((4 : ℝ) * b) - 1) := by
    clear * - h_step4 hb
    simp_all only [delta]
    (field_simp)
    (nlinarith)

  have h_step6_expand : (Real.sqrt a + Real.sqrt b) ^ 2 = a + 2 * Real.sqrt (a * b) + b := by
    clear * - ha hb
    (field_simp)
    (ring_nf at *)
    (field_simp)

  have h_step6 : ((Real.sqrt a + Real.sqrt b) ^ 2) / ((4 : ℝ) * b) - 1 = (a + 2 * Real.sqrt (a * b) + b - 4 * b) / ((4 : ℝ) * b) := by
    clear * - h_step6_expand hb
    simp_all only
    (field_simp)

  have h_step7_simp : a + 2 * Real.sqrt (a * b) + b - 4 * b = a + 2 * Real.sqrt (a * b) - 3 * b := by
    clear * -
    (nlinarith)

  have h_step7_factor : a + 2 * Real.sqrt (a * b) - 3 * b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + 3 * Real.sqrt b) := by
    clear * - ha hb
    (field_simp)
    (ring_nf at *)
    (field_simp)
    (nlinarith)

  have h_step7_term : (a + 2 * Real.sqrt (a * b) + b - 4 * b) / ((4 : ℝ) * b) = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + 3 * Real.sqrt b) / ((4 : ℝ) * b) := by
    clear * - h_step7_simp h_step7_factor hb
    simp_all only

  have h_step8 : delta = (Real.sqrt a - Real.sqrt b) ^ 2 / (2 : ℝ) * ((Real.sqrt a - Real.sqrt b) * (Real.sqrt a + 3 * Real.sqrt b) / ((4 : ℝ) * b)) := by
    clear * - h_step5 h_step6 h_step7_term
    simp_all only [delta]

  have h_step9 : delta = (Real.sqrt a - Real.sqrt b) ^ 3 * (Real.sqrt a + 3 * Real.sqrt b) / ((8 : ℝ) * b) := by
    clear * - h_step8 hb
    simp_all only [delta]
    (field_simp)
    (nlinarith)

  have h_sqrt_monotone : Real.sqrt b ≤ Real.sqrt a := by
    clear * - h₁ ha hb
    (field_simp)
    simp_all only

  have h_diff_nonneg : 0 ≤ Real.sqrt a - Real.sqrt b := by
    clear * - h_sqrt_monotone
    simp_all only [sub_nonneg]

  have h_cube_nonneg : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 3 := by
    clear * - h_diff_nonneg
    simp_all only [sub_nonneg, pow_nonneg]

  have h_sum_pos : 0 < Real.sqrt a + 3 * Real.sqrt b := by
    clear * - ha hb
    (positivity)

  have h_denom_pos : 0 < (8 : ℝ) * b := by
    clear * - hb
    simp_all only [ofNat_pos, mul_pos_iff_of_pos_left]

  have h_delta_nonneg : 0 ≤ delta := by
    clear * - h_step9 h_cube_nonneg h_sum_pos h_denom_pos
    simp_all only [ofNat_pos, mul_pos_iff_of_pos_left, delta]
    (bound )

  have h_final : (a + b) / (2 : ℝ) - Real.sqrt (a * b) ≤ (a - b) ^ 2 / ((8 : ℝ) * b) := by
    clear * - h_delta_nonneg
    simp_all only [sub_nonneg, tsub_le_iff_right, delta]

  exact h_final