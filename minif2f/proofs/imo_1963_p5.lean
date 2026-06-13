import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem imo_1963_p5 : Real.cos (Real.pi / 7) - Real.cos (2 * Real.pi / 7) + Real.cos (3 * Real.pi / 7) = 1 / 2 := by
  let θ := Real.pi / (7 : ℝ)

  let S := Real.cos θ - Real.cos (2 * θ) + Real.cos (3 * θ)

  have h_step3 : 2 * Real.sin θ * S = 2 * Real.sin θ * Real.cos θ - 2 * Real.sin θ * Real.cos (2 * θ) + 2 * Real.sin θ * Real.cos (3 * θ) := by
    clear * - θ S
    simp_all only [θ, S]
    (field_simp)
    (nlinarith)

  have h_step4 : 2 * Real.sin θ * Real.cos θ = Real.sin (2 * θ) := by
    clear * - θ
    simp_all only [θ]
    rw [← sin_two_mul, two_mul, add_comm]

  have h_step5 : 2 * Real.sin θ * Real.cos (2 * θ) = Real.sin (3 * θ) - Real.sin θ := by
    clear * - θ
    simp_all only [θ]
    simp [two_mul, sin_add, sin_sub, cos_add, cos_sub]
    simp only [sin_three_mul, cos_three_mul]
    ring
    simp_all only [one_div]
    simp [cos_sq']
    ring_nf

  have h_step6 : 2 * Real.sin θ * Real.cos (3 * θ) = Real.sin (4 * θ) - Real.sin (2 * θ) := by
    clear * - θ
    simp_all only [θ]
    simp [sin_sub_sin]
    ring_nf

  have h_step9 : 2 * Real.sin θ * S = Real.sin θ - Real.sin (3 * θ) + Real.sin (4 * θ) := by
    clear * - h_step3 h_step4 h_step5 h_step6
    simp_all [θ, S]
    (field_simp)
    (nlinarith)

  have h_step12 : 7 * θ = Real.pi := by
    clear * - θ
    simp_all only [θ]
    (ring)

  have h_step13 : 4 * θ = Real.pi - 3 * θ := by
    clear * - h_step12 θ
    simp_all only [θ]
    (field_simp)
    (nlinarith)

  have h_step15 : Real.sin (4 * θ) = Real.sin (3 * θ) := by
    clear * - h_step13
    simp_all only [sin_pi_sub, θ]

  have h_step17 : 2 * Real.sin θ * S = Real.sin θ := by
    clear * - h_step9 h_step15
    simp_all only [sub_add_cancel, θ, S]

  have h_sin_nonzero : Real.sin θ ≠ 0 := by
    clear * - θ h_step12
    simp_all only [ne_eq, θ]
    apply (sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) (by linarith [pi_pos])).ne'

  have h_step19 : S = (1 : ℝ) / 2 := by
    clear * - h_step17 h_sin_nonzero
    simp_all only [ne_eq, one_div, θ, S]
    apply mul_left_cancel₀ h_sin_nonzero <;> linarith

  have h_step20 : Real.cos (Real.pi / 7) - Real.cos (2 * Real.pi / 7) + Real.cos (3 * Real.pi / 7) = (1 : ℝ) / 2 := by
    clear * - h_step19 S
    simp_all only [one_div, S, θ]
    ring_nf at * <;> simp_all

  exact h_step20