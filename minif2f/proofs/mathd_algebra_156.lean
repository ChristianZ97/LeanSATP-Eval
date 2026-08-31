import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have h_step_1 : x ^ 4 = (5 : ℝ) * x ^ 2 - (6 : ℝ) := by
    clear * - h₀ h₁ h₂
    simp_all only

  have h_step_2 : x ^ 4 - ((5 : ℝ) * x ^ 2) + (6 : ℝ) = 0 := by
    clear * - h_step_1
    simp_all only [sub_sub_cancel_left, neg_add_cancel]

  have h_step_3 : ((x ^ 2) - (2 : ℝ)) * ((x ^ 2) - (3 : ℝ)) = 0 := by
    clear * - h_step_2
    simp_all only [_root_.mul_eq_zero]
    (grind only [integral_gaussian])

  have h_step_4 : y ^ 4 = (5 : ℝ) * y ^ 2 - (6 : ℝ) := by
    clear * - h₀ h₁ h₃
    simp_all only

  have h_step_5 : y ^ 4 - ((5 : ℝ) * y ^ 2) + (6 : ℝ) = 0 := by
    clear * - h_step_4
    simp_all only [sub_sub_cancel_left, neg_add_cancel]

  have h_step_6 : ((y ^ 2) - (2 : ℝ)) * ((y ^ 2) - (3 : ℝ)) = 0 := by
    clear * - h_step_5
    simp_all only [_root_.mul_eq_zero]
    (grind only [mul_self_nonneg])

  have h_root_x : x ^ 2 = (2 : ℝ) ∨ x ^ 2 = (3 : ℝ) := by
    clear * - h_step_3
    simp_all only [_root_.mul_eq_zero]
    (grind only [zero_lt_two])

  have h_root_y : y ^ 2 = (2 : ℝ) ∨ y ^ 2 = (3 : ℝ) := by
    clear * - h_step_6
    simp_all only [_root_.mul_eq_zero]
    (grind only [sq_eq_sq_iff_eq_or_eq_neg])

  have h_step_8 : x ^ 2 = (2 : ℝ) := by
    clear * - h₄ h_root_x h_root_y
    (bound )

  have h_step_9 : y ^ 2 = (3 : ℝ) := by
    clear * - h₄ h_root_y h_step_8
    simp_all only
    (bound )

  have h_step_10 : y ^ 2 - x ^ 2 = (3 : ℝ) - (2 : ℝ) := by
    clear * - h_step_8 h_step_9
    simp_all only

  have h_step_11 : y ^ 2 - x ^ 2 = (1 : ℝ) := by
    clear * - h_step_10
    simp_all only
    (linarith)

  exact h_step_11
