import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem aime_1983_p2 (x p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15) (h₁ : p ≤ x ∧ x ≤ 15)
    (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : 15 ≤ f x := by
  have h₃ : p ≤ x := by
    clear * - h₁
    simp_all only

  have h₄ : x ≤ (15:ℝ) := by
    clear * - h₁
    simp_all only

  have h₅ : (0:ℝ) < p := by
    clear * - h₀
    simp_all only

  have h₆ : p < (15:ℝ) := by
    clear * - h₀
    simp_all only

  have h₇ : abs (x - p) = x - p := by
    clear * - h₃
    simp_all only [abs_eq_self, sub_nonneg]

  have h₈ : x - (15:ℝ) ≤ 0 := by
    clear * - h₄
    simp_all only [tsub_le_iff_right, zero_add]

  have h₉ : abs (x - (15:ℝ)) = -(x - (15:ℝ)) := by
    clear * - h₈
    simp_all only [tsub_le_iff_right, zero_add, neg_sub]
    have := h₈
    simp_all only
    rw [abs_of_nonpos] <;> linarith [this, sub_nonpos_of_le this]

  have h₁₀ : -p < (0:ℝ) := by
    clear * - h₅
    simp_all only [Left.neg_neg_iff]

  have h₁₁ : x - (15:ℝ) - p < (0:ℝ) := by
    clear * - h₈ h₁₀
    simp_all only [tsub_le_iff_right, zero_add, Left.neg_neg_iff, sub_neg]
    (nlinarith)

  have h₁₂ : x - p - (15:ℝ) < (0:ℝ) := by
    clear * - h₁₁
    simp_all only [sub_neg]
    (nlinarith)

  have h₁₃ : abs (x - p - (15:ℝ)) = -(x - p - (15:ℝ)) := by
    clear * - h₁₂
    simp_all only [sub_neg, neg_sub]
    cases' abs_cases (x - p - 15) with h h <;> linarith

  have h₁₄ : abs (x - p - (15:ℝ)) = -x + p + (15:ℝ) := by
    clear * - h₁₃
    simp_all only [neg_sub]
    (nlinarith)

  have h₁₅ : f x = (x - p) + (-(x - (15:ℝ))) + (-x + p + (15:ℝ)) := by
    clear * - h₂ h₇ h₉ h₁₄
    simp_all only [neg_sub, sub_add_sub_cancel', abs_eq_self, sub_nonneg]

  have h₁₆ : f x = x - p - x + (15:ℝ) - x + p + (15:ℝ) := by
    clear * - h₁₅
    simp_all only [neg_sub, sub_add_sub_cancel', sub_sub_cancel_left]
    (nlinarith)

  have h₁₇ : f x = (x - x - x) + (-p + p) + ((15:ℝ) + (15:ℝ)) := by
    clear * - h₁₆
    simp_all only [sub_sub_cancel_left, sub_self, zero_sub, neg_add_cancel, add_zero]
    (nlinarith)

  have h₁₈ : f x = -x + (0:ℝ) + (30:ℝ) := by
    clear * - h₁₇
    simp_all only [sub_self, zero_sub, neg_add_cancel, add_zero, add_right_inj]
    (nlinarith)

  have h₁₉ : f x = (30:ℝ) - x := by
    clear * - h₁₈
    simp_all only [add_zero]
    (nlinarith)

  have h₂₀ : -x ≥ -(15:ℝ) := by
    clear * - h₄
    simp_all only [ge_iff_le, neg_le_neg_iff]

  have h₂₁ : (30:ℝ) - x ≥ (15:ℝ) := by
    clear * - h₂₀
    simp_all only [ge_iff_le, neg_le_neg_iff]
    (nlinarith)

  have h₂₂ : (15:ℝ) ≤ f x := by
    clear * - h₁₉ h₂₁
    simp_all only [ge_iff_le]

  exact h₂₂