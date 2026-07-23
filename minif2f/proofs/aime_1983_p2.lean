import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

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
    (ring)
    (linarith)

  have h₆ : p < (15:ℝ) := by
    clear * - h₀
    (ring)
    (linarith)

  have h₇ : abs (x - p) = x - p := by
    clear * - h₃
    (simp_all)

  have h₈ : x - (15:ℝ) ≤ 0 := by
    clear * - h₄
    simp_all only [tsub_le_iff_right, zero_add]

  have h₉ : abs (x - (15:ℝ)) = -(x - (15:ℝ)) := by
    clear * - h₈
    rw [abs_eq_neg_self.mpr] <;> linarith [abs_nonneg (x - 15)]

  have h₁₀ : -p < (0:ℝ) := by
    clear * - h₅
    simp_all only [Left.neg_neg_iff]

  have h₁₁ : x - (15:ℝ) - p < (0:ℝ) := by
    clear * - h₈ h₁₀
    simp only [tsub_le_iff_right, zero_add, Left.neg_neg_iff, sub_neg] at *
    (ring)
    simp only [neg_add_lt_iff_lt_add] at *
    (ring)
    (linarith)

  have h₁₂ : x - p - (15:ℝ) < (0:ℝ) := by
    clear * - h₁₁
    (ring)
    (linarith)

  have h₁₃ : abs (x - p - (15:ℝ)) = -(x - p - (15:ℝ)) := by
    clear * - h₁₂
    apply abs_of_neg <;> linarith

  have h₁₄ : abs (x - p - (15:ℝ)) = -x + p + (15:ℝ) := by
    clear * - h₁₃
    simp_all only [neg_sub]
    (grind only [div_eq_mul_inv])

  have h₁₅ : f x = (x - p) + (-(x - (15:ℝ))) + (-x + p + (15:ℝ)) := by
    clear * - h₂ h₇ h₉ h₁₄
    (linarith)

  have h₁₆ : f x = x - p - x + (15:ℝ) - x + p + (15:ℝ) := by
    clear * - h₁₅
    (linarith)

  have h₁₇ : f x = (x - x - x) + (-p + p) + ((15:ℝ) + (15:ℝ)) := by
    clear * - h₁₆
    (linarith)

  have h₁₈ : f x = -x + (0:ℝ) + (30:ℝ) := by
    clear * - h₁₇
    (linarith)

  have h₁₉ : f x = (30:ℝ) - x := by
    clear * - h₁₈
    (linarith)

  have h₂₀ : -x ≥ -(15:ℝ) := by
    clear * - h₄
    simp_all only [ge_iff_le, neg_le_neg_iff]

  have h₂₁ : (30:ℝ) - x ≥ (15:ℝ) := by
    clear * - h₂₀
    linarith [-x ≥ -15]

  have h₂₂ : (15:ℝ) ≤ f x := by
    clear * - h₁₉ h₂₁
    simp_all only [ge_iff_le]

  exact h₂₂
