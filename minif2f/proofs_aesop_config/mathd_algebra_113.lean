import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have h1 : x ^ 2 - (14 : ℝ) * x + (3 : ℝ) = x ^ 2 - (14 : ℝ) * x + (49 : ℝ) - (49 : ℝ) + (3 : ℝ) := by
    clear * -
    simp_all only [add_sub_cancel_right]

  have h2 : x ^ 2 - (14 : ℝ) * x + (49 : ℝ) = (x - (7 : ℝ)) ^ 2 := by
    clear * -
    (nlinarith)

  have h3 : -(49 : ℝ) + (3 : ℝ) = -(46 : ℝ) := by
    clear * -
    (ring)

  have h4 : x ^ 2 - (14 : ℝ) * x + (3 : ℝ) = (x - (7 : ℝ)) ^ 2 - (46 : ℝ) := by
    clear * - h1 h2 h3
    simp_all only [add_left_inj, sub_add_cancel]
    (nlinarith)

  have h5 : (x - (7 : ℝ)) ^ 2 ≥ (0 : ℝ) := by
    clear * -
    simp_all only [ge_iff_le]
    (nlinarith)

  have h6 : (x - (7 : ℝ)) ^ 2 - (46 : ℝ) ≥ -(46 : ℝ) := by
    clear * - h5
    simp_all only [ge_iff_le, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]

  have h7 : (7 : ℝ) ^ 2 - (14 : ℝ) * (7 : ℝ) + (3 : ℝ) = (49 : ℝ) - (98 : ℝ) + (3 : ℝ) := by
    clear * -
    simp_all only [add_left_inj]
    (nlinarith)

  have h8 : (49 : ℝ) - (98 : ℝ) + (3 : ℝ) = -(49 : ℝ) + (3 : ℝ) := by
    clear * -
    simp only [add_left_inj] at *
    (ring)

  have h9 : -(49 : ℝ) + (3 : ℝ) = -(46 : ℝ) := by
    clear * -
    (ring)

  have h_rhs_val : (7 : ℝ) ^ 2 - (14 : ℝ) * (7 : ℝ) + (3 : ℝ) = -(46 : ℝ) := by
    clear * - h7 h8 h9
    simp_all only

  have h10 : x ^ 2 - (14 : ℝ) * x + (3 : ℝ) ≥ (7 : ℝ) ^ 2 - (14 : ℝ) * (7 : ℝ) + (3 : ℝ) := by
    clear * - h4 h6 h_rhs_val
    simp_all only [ge_iff_le, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]

  exact h10