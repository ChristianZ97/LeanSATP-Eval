import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_17 (a : ℝ)
    (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) : a = 8 := by
  have h1 : (16:ℝ) + 16 * a = 16 * (1 + a) := by
    clear * -
    (nlinarith)

  have h2 : Real.sqrt (16 + 16 * a) = 4 * Real.sqrt (1 + a) := by
    clear * - h1
    simp_all only [ofNat_nonneg, sqrt_mul, mul_eq_mul_right_iff]
    refine .inl (by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num)

  have h3 : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by
    clear * - h₀ h2
    simp_all only

  have h4 : (4:ℝ) + 4 * Real.sqrt (1 + a) = 4 * (1 + Real.sqrt (1 + a)) := by
    clear * -
    (nlinarith)

  have h5 : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) = Real.sqrt (4 * (1 + Real.sqrt (1 + a))) := by
    clear * - h4
    simp_all only [ofNat_nonneg, sqrt_mul]

  have h6 : Real.sqrt (4 * (1 + Real.sqrt (1 + a))) = Real.sqrt 4 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    clear * -
    simp_all only [ofNat_nonneg, sqrt_mul]

  have h7 : Real.sqrt 4 = (2:ℝ) := by
    clear * -
    simp [show (4 : ℝ) = (2 * 2 : ℝ) by norm_num]

  have h8 : Real.sqrt (4 * (1 + Real.sqrt (1 + a))) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    clear * - h6 h7
    simp_all only [ofNat_nonneg, sqrt_mul]

  have h9 : 2 * Real.sqrt (1 + Real.sqrt (1 + a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = (6:ℝ) := by
    clear * - h3 h5 h8
    simp_all only [ofNat_nonneg, sqrt_mul, mul_eq_mul_right_iff]

  have h10 : (3:ℝ) * Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by
    clear * - h9
    (nlinarith)

  have h11 : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by
    clear * - h10
    (nlinarith)

  have h12 : (1:ℝ) + Real.sqrt (1 + a) = 4 := by
    clear * - h11
    rw [Real.sqrt_eq_iff_sq_eq] at h11
    · linarith [show ((2 : ℝ) : ℝ) ^ 2 = 4 by norm_num]
    · exact le_of_lt (by linarith [Real.sqrt_pos.1 (by linarith)])
    · simp_all only [ofNat_nonneg]

  have h13 : Real.sqrt (1 + a) = 3 := by
    clear * - h12
    (nlinarith)

  have h14 : (1:ℝ) + a = 9 := by
    clear * - h13
    try rw [Real.sqrt_eq_iff_sq_eq] at h13
    · linarith
    · exact le_of_lt (Real.sqrt_pos.1 <| by linarith)
    · simp_all only [ofNat_nonneg]

  have h15 : a = (8:ℝ) := by
    clear * - h14
    (nlinarith)

  exact h15