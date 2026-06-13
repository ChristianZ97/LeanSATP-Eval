import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  have h1 : (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = (16 * ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) := by
    have h1_inner : a ^ 2 = (8 : ℝ) ^ 2 := by
      clear * - h₀
      subst h₀
      simp_all only

    clear * - h1_inner
    simp_all only [one_div]

  have h2 : (16 * ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = (16 * (64 : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) := by
    have h2_fact : ((8 : ℝ) ^ 2) = (64 : ℝ) := by
      clear * -
      (ring)

    clear * - h2_fact
    simp_all only [one_div]

  have h3 : (16 * (64 : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = (16 * (4 : ℝ)) ^ ((1 : ℝ) / 3) := by
    have h3_fact : (64 : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
      clear * -
      simp_all only [one_div]
      rw [Real.rpow_def_of_pos (by norm_num)] <;> norm_cast
      field_simp [show (64 : ℝ) = 2 ^ 6 by norm_cast] <;> ring
      simp [exp_mul, exp_log] <;> norm_num

    clear * - h3_fact
    simp_all only [one_div]

  have h4 : (16 * (4 : ℝ)) ^ ((1 : ℝ) / 3) = (64 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h4_fact : (16 : ℝ) * (4 : ℝ) = (64 : ℝ) := by
      clear * -
      (ring)

    clear * - h4_fact
    simp only [one_div] at *
    (ring)

  have h5 : (64 : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
    have h5_fact : (64 : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
      clear * -
      simp_all only [one_div]
      rw [eq_comm]
      have : (64 : ℝ) = (4 : ℝ) ^ 3
      · norm_num
      · simp_all only
        simp [← this, Real.rpow_def_of_pos]
        simp_all only [Real.log_pow, Nat.cast_ofNat]
        field_simp [exp_log, mul_comm] <;> ring

    clear * - h5_fact
    simp_all only [one_div]

  have h_final : (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
    clear * - h1 h2 h3 h4 h5
    simp_all only [one_div]

  exact h_final
