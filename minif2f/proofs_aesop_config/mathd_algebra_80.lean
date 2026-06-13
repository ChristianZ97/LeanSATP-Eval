import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by
  have h_step_2 : (x - 9 : ℝ) = (2 : ℝ) * (x + 1) := by
    clear * - h₀ h₁
    simp_all only [ne_eq]
    by_cases hx : x + 1 = 0 <;> field_simp [hx] at h₁ ⊢ <;> linarith

  have h_step_3_expand : (2 : ℝ) * (x + 1) = (2 : ℝ) * x + (2 : ℝ) := by
    clear * -
    (nlinarith)

  have h_step_3 : (x - 9 : ℝ) = (2 : ℝ) * x + (2 : ℝ) := by
    clear * - h_step_2 h_step_3_expand
    simp_all only

  have h_step_4 : (x - 9 : ℝ) - ((2 : ℝ) * x) = (2 : ℝ) := by
    clear * - h_step_3
    simp_all only [add_sub_cancel_left]

  have h_step_5 : -((x : ℝ)) - (9 : ℝ) = (2 : ℝ) := by
    clear * - h_step_4
    (nlinarith)

  have h_step_6 : -((x : ℝ)) = (11 : ℝ) := by
    clear * - h_step_5
    (nlinarith)

  have h_step_7 : x = (-11 : ℝ) := by
    clear * - h_step_6
    (nlinarith)

  exact h_step_7