import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have h1 : abs a + abs b ≥ abs (a + b) := by
    clear * -
    simp_all only [ge_iff_le]
    cases abs_cases (a + b) <;> cases abs_cases a <;> cases abs_cases b <;> linarith

  have h2 : abs a + abs b - abs (a + b) ≥ 0 := by
    clear * - h1
    simp_all only [ge_iff_le, sub_nonneg]

  have h3_a : (1:ℝ) + abs a > 0 := by
    clear * -
    simp_all only [gt_iff_lt]
    (positivity)

  have h3_b : (1:ℝ) + abs b > 0 := by
    clear * -
    simp_all only [gt_iff_lt]
    (positivity)

  have h3_ab : (1:ℝ) + abs (a + b) > 0 := by
    clear * -
    simp_all only [gt_iff_lt]
    (positivity)

  have h3_sum : (1:ℝ) + abs a + abs b > 0 := by
    clear * - h3_a h3_b
    simp_all only [gt_iff_lt]
    (positivity)

  have h3_prod : ((1:ℝ) + abs a + abs b) * ((1:ℝ) + abs (a + b)) > 0 := by
    clear * - h3_sum h3_ab
    simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left]

  have h4_id :
      (abs a + abs b) / ((1:ℝ) + abs a + abs b) - abs (a + b) / ((1:ℝ) + abs (a + b)) =
      (abs a + abs b - abs (a + b)) / (((1:ℝ) + abs a + abs b) * ((1:ℝ) + abs (a + b))) := by
    clear * -
    (field_simp)
    (nlinarith)

  have h7 : (abs a + abs b - abs (a + b)) / (((1:ℝ) + abs a + abs b) * ((1:ℝ) + abs (a + b))) ≥ 0 := by
    clear * - h2 h3_prod
    simp_all only [ge_iff_le, sub_nonneg, gt_iff_lt]
    (bound )

  have h8 : (abs a + abs b) / ((1:ℝ) + abs a + abs b) - abs (a + b) / ((1:ℝ) + abs (a + b)) ≥ 0 := by
    clear * - h4_id h7
    simp_all only [ge_iff_le]

  have h9 : abs (a + b) / ((1:ℝ) + abs (a + b)) ≤ (abs a + abs b) / ((1:ℝ) + abs a + abs b) := by
    clear * - h8
    simp_all only [ge_iff_le, sub_nonneg]

  have h10 : (abs a + abs b) / ((1:ℝ) + abs a + abs b) = abs a / ((1:ℝ) + abs a + abs b) + abs b / ((1:ℝ) + abs a + abs b) := by
    clear * -
    (field_simp)

  have h11 : (1:ℝ) + abs a + abs b ≥ (1:ℝ) + abs a := by
    clear * -
    simp_all only [ge_iff_le, le_add_iff_nonneg_right, abs_nonneg]

  have h12 : abs a / ((1:ℝ) + abs a + abs b) ≤ abs a / ((1:ℝ) + abs a) := by
    clear * - h11 h3_sum h3_a
    simp_all only [gt_iff_lt, ge_iff_le, le_add_iff_nonneg_right, abs_nonneg]
    (bound )

  have h13 : (1:ℝ) + abs a + abs b ≥ (1:ℝ) + abs b := by
    clear * -
    simp_all only [ge_iff_le, add_le_add_iff_right, le_add_iff_nonneg_right, abs_nonneg]

  have h14 : abs b / ((1:ℝ) + abs a + abs b) ≤ abs b / ((1:ℝ) + abs b) := by
    clear * - h13 h3_sum h3_b
    simp_all only [gt_iff_lt, ge_iff_le, add_le_add_iff_right, le_add_iff_nonneg_right, abs_nonneg]
    (bound )

  have h15 : abs a / ((1:ℝ) + abs a + abs b) + abs b / ((1:ℝ) + abs a + abs b) ≤ abs a / ((1:ℝ) + abs a) + abs b / ((1:ℝ) + abs b) := by
    clear * - h12 h14
    gcongr

  have h16 : abs (a + b) / ((1:ℝ) + abs (a + b)) ≤ abs a / ((1:ℝ) + abs a) + abs b / ((1:ℝ) + abs b) := by
    clear * - h9 h10 h15
    simp_all only
    linarith

  exact h16