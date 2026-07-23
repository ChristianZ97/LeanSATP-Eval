import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12b_2002_p19 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a * (b + c) = 152)
    (h₂ : b * (c + a) = 162) (h₃ : c * (a + b) = 170) : a * b * c = 720 := by
  have h_step1 : a * b + a * c = (152 : ℝ) := by
    clear * - h₁
    (linarith)

  have h_step2 : b * c + b * a = (162 : ℝ) := by
    clear * - h₂
    (linarith)

  have h_step3 : a * c + b * c = (170 : ℝ) := by
    clear * - h₃
    (linarith)

  have h_step6 : 2 * (a * b + b * c + a * c) = (484 : ℝ) := by
    clear * - h_step1 h_step2 h_step3
    (linarith)

  have h_step7 : a * b + b * c + a * c = (242 : ℝ) := by
    clear * - h_step6
    (linarith)

  have h_step9 : a * b = (72 : ℝ) := by
    clear * - h_step7 h_step3
    (linarith)

  have h_step11 : b * c = (90 : ℝ) := by
    clear * - h_step7 h_step1
    (linarith)

  have h_step13 : a * c = (80 : ℝ) := by
    clear * - h_step7 h_step2
    (linarith)

  have h_step15 : (a * b * c) ^ 2 = a * b * b * c * a * c := by
    clear * -
    (linarith)

  have h_step17 : (a * b * c) ^ 2 = (518400 : ℝ) := by
    clear * - h_step15 h_step9 h_step11 h_step13
    simp_all only
    (nlinarith)

  have h_step21 : a * b * c = (720 : ℝ) := by
    clear * - h_step17 h₀
    have h_sign := mul_pos (mul_pos h₀.1 h₀.2.1) h₀.2.2
    all_goals nlinarith [sq_nonneg (a * b * c), h_sign, h_step17]

  exact h_step21
