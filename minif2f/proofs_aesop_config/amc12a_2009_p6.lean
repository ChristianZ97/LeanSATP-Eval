import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12a_2009_p6 (m n p q : ℝ) (h₀ : p = 2 ^ m) (h₁ : q = 3 ^ n) :
  p ^ (2 * n) * q ^ m = 12 ^ (m * n) := by
  have h_step1 : p ^ (2 * n) * q ^ m = (2 ^ m) ^ (2 * n) * (3 ^ n) ^ m := by
    clear * - h₀ h₁
    subst h₁ h₀
    simp_all only

  simp_all only
  field_simp [Real.rpow_def_of_pos] <;> ring
  simp [← exp_add, mul_assoc, mul_comm, mul_left_comm]
  simp [show (12 : ℝ) = 2 ^ 2 * 3 by norm_cast, Real.log_mul, mul_left_comm] <;> ring