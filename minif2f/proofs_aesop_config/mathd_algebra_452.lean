import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
  have h_midpoint : a 5 = ((a 1) + (a 9)) / (2 : ℝ) := by
    clear * - h₀
    have t₂ := h₀ 4
    simp_all only [reduceAdd, zero_add]
    nlinarith [h₀ 1, h₀ 2, h₀ 3, h₀ 4, h₀ 5, h₀ 6, h₀ 7, h₀ 8, h₀ 9]

  have h_sum_sub_a1 : (a 1) + (a 9) = ((2 : ℝ) / (3 : ℝ)) + (a 9) := by
    clear * - h₁
    simp_all only

  have h_sum_sub_a9 : ((2 : ℝ) / (3 : ℝ)) + (a 9) = ((2 : ℝ) / (3 : ℝ)) + ((4 : ℝ) / (5 : ℝ)) := by
    clear * - h₂
    simp_all only

  have h_total_sum : (a 1) + (a 9) = ((2 : ℝ) / (3 : ℝ)) + ((4 : ℝ) / (5 : ℝ)) := by
    clear * - h_sum_sub_a1 h_sum_sub_a9
    simp_all only [add_right_inj, add_left_inj]

  have h_fraction_sum : ((2 : ℝ) / (3 : ℝ)) + ((4 : ℝ) / (5 : ℝ)) = (22 : ℝ) / (15 : ℝ) := by
    clear * -
    (field_simp)
    (ring)

  have h_sum_value : (a 1) + (a 9) = (22 : ℝ) / (15 : ℝ) := by
    clear * - h_total_sum h_fraction_sum
    simp_all only

  have h_avg_calc : ((22 : ℝ) / (15 : ℝ)) / (2 : ℝ) = (11 : ℝ) / (15 : ℝ) := by
    clear * -
    (ring)

  have h_final : a 5 = (11 : ℝ) / (15 : ℝ) := by
    clear * - h_midpoint h_sum_value h_avg_calc
    simp_all only

  exact h_final