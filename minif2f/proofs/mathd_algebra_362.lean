import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_362 (a b : ℝ) (h₀ : a ^ 2 * b ^ 3 = 32 / 27) (h₁ : a / b ^ 3 = 27 / 4) :
    a + b = 8 / 3 := by
  have h2 : a ^ 2 * b ^ 3 * (a / b ^ 3) = (32 / 27) * (27 / 4) := by
    clear * - h₀ h₁
    simp_all only

  have h3 : a ^ 3 = 8 := by
    clear * - h2
    (grind only [Pell.IsFundamental.x_mul_y_le_y_mul_x])

  have h4 : a = (2 : ℝ) := by
    clear * - h3
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a ^ 2 - 4)]

  have h5 : (2 : ℝ) / b ^ 3 = 27 / 4 := by
    clear * - h4 h₁
    simp_all only

  have h6 : b ^ 3 = 8 / 27 := by
    clear * - h5
    (grind only [mul_div_assoc])

  have h7 : b = (2 : ℝ) / 3 := by
    clear * - h6
    nlinarith [sq_nonneg (b ^ 2 - 4 / 9)]

  have h8 : a + b = (2 : ℝ) + (2 : ℝ) / 3 := by
    clear * - h4 h7
    (linarith)

  have h9 : a + b = 8 / 3 := by
    clear * - h8
    (linarith)

  exact h9
