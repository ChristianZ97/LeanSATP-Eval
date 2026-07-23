import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem aime_1987_p5 (x y : ℤ) (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    3 * (x ^ 2 * y ^ 2) = 588 := by
  have h₁ : y ^ 2 * (1 + 3 * x ^ 2) = 30 * x ^ 2 + 517 := by
    clear * - h₀
    (linarith)

  have h₂ : 30 * x ^ 2 = 10 * (3 * x ^ 2 + 1) - 10 := by
    clear * -
    (linarith)

  have h₃ : y ^ 2 * (1 + 3 * x ^ 2) = 10 * (3 * x ^ 2 + 1) + 507 := by
    clear * - h₁ h₂
    simp_all only
    (linarith)

  have h₄ : y ^ 2 * (1 + 3 * x ^ 2) - 10 * (3 * x ^ 2 + 1) = 507 := by
    clear * - h₃
    simp_all only [add_sub_cancel_left]

  have h₅ : (y ^ 2 - 10) * (3 * x ^ 2 + 1) = 507 := by
    clear * - h₄
    (linarith)

  have h₆ : 507 = 3 * 13 ^ 2 := by
    clear * -
    simp only [reducePow, reduceMul] at *

  have h₇ : 3 * x ^ 2 + 1 = 13 := by
    clear * - h₅ h₆
    have key := h₅
    have : y ^ 2 - 10 ≤ 507 := by nlinarith
    on_goal 1 =>
    have : y ^ 2 ≤ 517 := by omega
    have : y ≤ 22 := by nlinarith
    have : y ≥ -22 := by nlinarith
    interval_cases y <;> omega

  have h₈ : 3 * x ^ 2 = 12 := by
    clear * - h₇
    (linarith)

  have h₉ : x ^ 2 = 4 := by
    clear * - h₈
    (nlinarith)

  have h₁₀ : y ^ 2 - 10 = 39 := by
    clear * - h₅ h₇
    (nlinarith)

  have h₁₁ : y ^ 2 = 49 := by
    clear * - h₁₀
    (linarith)

  have h₁₂ : 3 * (x ^ 2 * y ^ 2) = 3 * 4 * 49 := by
    clear * - h₉ h₁₁
    simp_all only
    (linarith)

  have h₁₃ : 3 * (x ^ 2 * y ^ 2) = 588 := by
    clear * - h₁₂
    simp only [Int.reduceMul] at *
    (linarith)

  exact h₁₃
