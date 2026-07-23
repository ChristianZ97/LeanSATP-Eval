import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem imo_1960_p2 (x : ℝ) (h₀ : 0 ≤ 1 + 2 * x) (h₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0)
    (h₂ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9) : -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  have h_step2 : (2:ℝ) * x = (1 + 2 * x) - 1 := by
    clear * -
    simp_all only [add_sub_cancel_left]

  have h_step3 : 4 * x ^ 2 = ((1 + 2 * x) - 1) ^ 2 := by
    clear * - h_step2
    simp_all only [add_sub_cancel_left]
    (linarith)

  have h_step4 : (1 + 2 * x) - 1 = (Real.sqrt (1 + 2 * x) - 1) * (Real.sqrt (1 + 2 * x) + 1) := by
    clear * - h₀
    simp_all only [add_sub_cancel_left]
    (grind only [Real.mul_self_sqrt])

  have h_step5 : 4 * x ^ 2 = ((Real.sqrt (1 + 2 * x) - 1) * (Real.sqrt (1 + 2 * x) + 1)) ^ 2 := by
    clear * - h_step3 h_step4
    simp [*, mul_pow]

  have h_step6 : 4 * x ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
    clear * - h_step5
    simp_all only
    (linarith)

  have h_step7 : (Real.sqrt (1 + 2 * x) - 1) ^ 2 = (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by
    clear * -
    (linarith)

  have h_step8 : 4 * x ^ 2 = (1 - Real.sqrt (1 + 2 * x)) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
    clear * - h_step6 h_step7
    simp_all only

  have h_step10 : (Real.sqrt (1 + 2 * x) + 1) ^ 2 < 2 * x + 9 := by
    clear * - h_step8 h₁ h₂
    have hm := sub_ne_zero.2 h₁
    simp_all [Ne.symm hm]

  have h_step11 : (Real.sqrt (1 + 2 * x) + 1) ^ 2 = (Real.sqrt (1 + 2 * x)) ^ 2 + 2 * Real.sqrt (1 + 2 * x) + 1 := by
    clear * -
    (linarith)

  have h_step12 : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
    clear * - h₀
    (simp_all)

  have h_step13 : (1 + 2 * x) + 2 * Real.sqrt (1 + 2 * x) + 1 < 2 * x + 9 := by
    clear * - h_step10 h_step11 h_step12
    (linarith)

  have h_step14 : 2 * Real.sqrt (1 + 2 * x) + 2 < 9 := by
    clear * - h_step13
    (linarith)

  have h_step15 : 2 * Real.sqrt (1 + 2 * x) < (7:ℝ) := by
    clear * - h_step14
    (linarith)

  have h_step16 : Real.sqrt (1 + 2 * x) < (7:ℝ) / 2 := by
    clear * - h_step15
    (nlinarith)

  have h_step17 : 1 + 2 * x < ((7:ℝ) / 2) ^ 2 := by
    clear * - h_step16
    rw [Real.sqrt_lt'] at h_step16 <;> nlinarith

  have h_step18 : 1 + 2 * x < (49:ℝ) / 4 := by
    clear * - h_step17
    (nlinarith)

  have h_step19 : 2 * x < (49:ℝ) / 4 - (1:ℝ) := by
    clear * - h_step18
    (linarith)

  have h_step20 : 2 * x < (45:ℝ) / 4 := by
    clear * - h_step19
    (linarith)

  have h_step21 : x < (45:ℝ) / 8 := by
    clear * - h_step20
    (linarith)

  have h_step24 : -((1:ℝ) / 2) ≤ x := by
    clear * - h₀
    simp_all only [one_div]
    (linarith)

  have h_step25 : -((1:ℝ) / 2) ≤ x ∧ x < (45:ℝ) / 8 := by
    clear * - h_step24 h_step21
    simp_all only [one_div, and_self]

  exact h_step25
