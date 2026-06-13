import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_208 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by
  have h1 : (1000000 : ℝ) = (10 : ℝ) ^ 6 := by
    clear * -
    (norm_num)

  have h2 : Real.sqrt 1000000 = Real.sqrt ((10 : ℝ) ^ 6) := by
    clear * - h1
    simp only [ofNat_nonneg, pow_nonneg, sqrt_inj] at *
    exact h1

  have h3 : Real.sqrt ((10 : ℝ) ^ 6) = ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 2) := by
    clear * -
    simp_all only [one_div]
    simp [Real.sqrt_eq_rpow, mul_comm]

  have h4 : ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 2) = (10 : ℝ) ^ (6 * ((1 : ℝ) / 2)) := by
    clear * -
    simp_all only [one_div]
    rw [rpow_mul] <;> norm_num

  have h5 : (6 : ℝ) * ((1 : ℝ) / 2) = 3 := by
    clear * -
    simp_all only [one_div]
    (ring)

  have h6 : (10 : ℝ) ^ (6 * ((1 : ℝ) / 2)) = (10 : ℝ) ^ 3 := by
    clear * - h5
    simp_all only [one_div]
    (nlinarith)

  have h7 : (10 : ℝ) ^ 3 = (1000 : ℝ) := by
    clear * -
    (ring)

  have h8 : Real.sqrt 1000000 = (1000 : ℝ) := by
    clear * - h2 h3 h4 h6 h7
    simp_all only [one_div]

  have h9 : 1000000 ^ ((1 : ℝ) / 3) = ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 3) := by
    clear * - h1
    simp_all only [one_div]

  have h10 : ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ (6 * ((1 : ℝ) / 3)) := by
    clear * -
    simp_all only [one_div]
    simp [Real.rpow_def_of_pos, mul_comm]
    rw [mul_assoc]

  have h11 : (6 : ℝ) * ((1 : ℝ) / 3) = 2 := by
    clear * -
    simp only [one_div] at *
    (field_simp)
    (ring)

  have h12 : (10 : ℝ) ^ (6 * ((1 : ℝ) / 3)) = (10 : ℝ) ^ 2 := by
    clear * - h11
    simp_all only [one_div, rpow_two]

  have h13 : (10 : ℝ) ^ 2 = (100 : ℝ) := by
    clear * -
    (ring)

  have h14 : 1000000 ^ ((1 : ℝ) / 3) = (100 : ℝ) := by
    clear * - h9 h10 h12 h13
    simp_all only [one_div]

  have h15 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = (1000 : ℝ) - (100 : ℝ) := by
    clear * - h8 h14
    simp_all only [one_div]

  have h16 : (1000 : ℝ) - (100 : ℝ) = 900 := by
    clear * -
    (ring)

  have h17 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by
    clear * - h15 h16
    simp_all only [one_div]

  exact h17