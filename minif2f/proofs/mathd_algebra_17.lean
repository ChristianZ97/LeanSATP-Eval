import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_17 (a : ℝ)
    (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) : a = 8 := by
  have h_step_2 : Real.sqrt (16 + 16 * a) = Real.sqrt (16 * (1 + a)) := by
    clear * -
    simp_all only [ofNat_nonneg, sqrt_mul]
    (ring)
    (field_simp)
    simp_all only [ofNat_nonneg, sqrt_mul]
    (ring)

  have h_step_3 : Real.sqrt (16 * (1 + a)) = 4 * Real.sqrt (1 + a) := by
    clear * -
    simp_all only [ofNat_nonneg, sqrt_mul, mul_eq_mul_right_iff]
    (norm_num [Quaternion.star_add_self] at *)

  have h_step_4 : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = Real.sqrt (4 + 4 * Real.sqrt (1 + a)) := by
    clear * - h_step_2 h_step_3
    simp_all only [ofNat_nonneg, sqrt_mul, mul_eq_mul_right_iff]

  have h_step_4b : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) = Real.sqrt (4 * (1 + Real.sqrt (1 + a))) := by
    clear * -
    simp_all only [ofNat_nonneg, sqrt_mul]
    (ring)
    (field_simp)
    simp_all only [ofNat_nonneg, sqrt_mul]
    (ring)

  have h_step_5 : Real.sqrt (4 * (1 + Real.sqrt (1 + a))) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    clear * -
    simp_all only [ofNat_nonneg, sqrt_mul, mul_eq_mul_right_iff]
    (field_simp [*] at *)
    (norm_num [Quaternion.self_add_star] at *)

  have h_lhs_simple : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    clear * - h_step_4 h_step_4b h_step_5
    simp_all only [ofNat_nonneg, sqrt_mul, mul_eq_mul_right_iff]

  have h_step_6 : 3 * Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by
    clear * - h₀ h_lhs_simple
    simp_all only
    (linarith)

  have h_step_7 : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by
    clear * - h_step_6
    (linarith)

  have h_step_8 : 1 + Real.sqrt (1 + a) = 4 := by
    clear * - h_step_7
    rw [Real.sqrt_eq_iff_mul_self_eq, eq_comm] at h_step_7
    · linarith [(by norm_num : (2 : ℝ) * (2 : ℝ) = 4)]
    · exact le_of_lt <| by nlinarith [Real.sqrt_nonneg (1 + a)]
    · linarith [Real.sqrt_nonneg (1 + √(1 + a))]

  have h_step_9 : Real.sqrt (1 + a) = 3 := by
    clear * - h_step_8
    (linarith)

  have h_step_10 : 1 + a = 9 := by
    clear * - h_step_9
    have H := Real.sqrt_nonneg (1 + a)
    have H' := h_step_9
    try rw [Real.sqrt_eq_iff_mul_self_eq] at *
    · linarith [show (3 : ℝ) * 3 = 9 by norm_num1, h_step_9]
    · linarith [Real.sqrt_pos.1 <| by linarith]
    · norm_num
    · exact le_of_lt <| Real.sqrt_pos.1 (by linarith)
    · exact le_of_lt (by simp)

  have h_step_11 : a = 8 := by
    clear * - h_step_10
    (linarith)

  exact h_step_11
