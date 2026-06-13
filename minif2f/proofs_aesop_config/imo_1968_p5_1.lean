import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a) (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) (h₂ : ∀ x, f x - f x ^ 2 ≥ 0) : ∃ b > 0, ∀ x, f (x + b) = f x := by
  use (2 * a)
  constructor
  · -- Step 1: Show b > 0
    have h_b_pos : 0 < (2 * a) := by
      clear * - h₀
      simp_all only [ofNat_pos, mul_pos_iff_of_pos_left]

    exact h_b_pos

  · -- Step 2: Show ∀ x, f (x + 2*a) = f x
    intro x

    have h_x_lower : f x ≥ (1 : ℝ) / 2 := by
      have h_prev : f x = (1 : ℝ) / 2 + Real.sqrt (f (x - a) - f (x - a) ^ 2) := by
        clear * - h₁
        simp_all only [one_div]
        have := h₁ (x - a)
        simp_all only [sub_add_cancel]

      clear * - h_prev
      simp_all only [one_div, ge_iff_le, le_add_iff_nonneg_right, Real.sqrt_nonneg]

    have h_f_x_plus_2a : f (x + (2 * a)) = (1 : ℝ) / 2 + Real.sqrt (f (x + a) - f (x + a) ^ 2) := by
      clear * - h₁
      simp_all only [one_div]
      have h₂ := h₁ ((x + a) - a)
      simp_all only [add_sub_cancel_right]
      have h := h₁ (x + a)
      simp_all only
      rw [show x + 2 * a = x + a + a by ring, h₁, h₁] <;> ring_nf

    have h_inside_sqrt : f (x + a) - f (x + a) ^ 2 = (f x - (1 : ℝ) / 2) ^ 2 := by
      clear * - h₁ h₂
      simp_all only [one_div, ge_iff_le, sub_nonneg]
      (field_simp)
      (ring_nf at *)
      simp_all only [one_div, sub_nonneg, sq_sqrt]
      (nlinarith)

    have h_sqrt_eval : Real.sqrt (f (x + a) - f (x + a) ^ 2) = f x - (1 : ℝ) / 2 := by
      clear * - h_inside_sqrt h_x_lower
      simp_all only [one_div, ge_iff_le, sub_nonneg, sqrt_sq]

    have h_final : f (x + (2 * a)) = f x := by
      clear * - h_f_x_plus_2a h_sqrt_eval
      simp_all only [one_div, add_sub_cancel]

    exact h_final