import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have h1 : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt ((60 * x) * (12 * x) * (63 * x)) := by
    clear * -
    simp_all only [ofNat_nonneg, sqrt_mul, ofNat_pos, mul_nonneg_iff_of_pos_left, NNReal.zero_le_coe, sqrt_mul']

  have h2 : ((60 * x) * (12 * x) * (63 * x) : ℝ) = (60 * 12 * 63 : ℝ) * x ^ 3 := by
    clear * -
    (nlinarith)

  have h3 : (60 * 12 * 63 : ℝ) = 45360 := by
    clear * -
    (ring)

  have h4 : (45360 : ℝ) = 36 ^ 2 * 35 := by
    clear * -
    (ring)

  have h5 : ((60 * x) * (12 * x) * (63 * x) : ℝ) = (36 ^ 2 : ℝ) * x ^ 2 * 35 * x := by
    clear * - h2 h3 h4
    simp_all only
    (nlinarith)

  have h6 : ((60 * x) * (12 * x) * (63 * x) : ℝ) = ((36 * x : ℝ) ^ 2) * (35 * x : ℝ) := by
    clear * - h5
    simp_all only
    (nlinarith)

  have h7 : Real.sqrt ((60 * x) * (12 * x) * (63 * x)) = Real.sqrt (((36 * x : ℝ) ^ 2) * (35 * x : ℝ)) := by
    clear * - h6
    simp_all only [ofNat_pos, mul_nonneg_iff_of_pos_left, NNReal.zero_le_coe, sqrt_mul', sqrt_sq, ofNat_nonneg, sqrt_mul]

  have h8 : Real.sqrt (((36 * x : ℝ) ^ 2) * (35 * x : ℝ)) = Real.sqrt ((36 * x : ℝ) ^ 2) * Real.sqrt (35 * x) := by
    clear * -
    simp_all only [ofNat_pos, mul_nonneg_iff_of_pos_left, NNReal.zero_le_coe, sqrt_mul', sqrt_sq, ofNat_nonneg, sqrt_mul]

  have h9 : Real.sqrt ((36 * x : ℝ) ^ 2) = 36 * x := by
    clear * -
    simp_all only [ofNat_pos, mul_nonneg_iff_of_pos_left, NNReal.zero_le_coe, sqrt_sq]

  have h10 : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
    clear * - h1 h7 h8 h9
    simp_all only [ofNat_nonneg, sqrt_mul, ofNat_pos, mul_nonneg_iff_of_pos_left, NNReal.zero_le_coe, sqrt_mul', sqrt_sq]

  exact h10