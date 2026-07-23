import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12a_2009_p7 (x : ℝ) (n : ℕ) (a : ℕ → ℝ)
    (h₁ : ∀ m, a (m + 1) - a m = a (m + 2) - a (m + 1)) (h₂ : a 1 = 2 * x - 3)
    (h₃ : a 2 = 5 * x - 11) (h₄ : a 3 = 3 * x + 1) (h₅ : a n = 2009) : n = 502 := by
  have h_step1 : a 2 - a 1 = a 3 - a 2 := by
    clear * - h₁
    linarith [h₁ 1, h₁ 2, h₁ 3, h₁ 4]

  have h_step2 : (5 * x - 11 : ℝ) - (2 * x - 3 : ℝ) = (3 * x + 1 : ℝ) - (5 * x - 11 : ℝ) := by
    clear * - h_step1 h₂ h₃ h₄
    (linarith)

  have h_step3 : (3 * x - 8 : ℝ) = (-2 * x + 12 : ℝ) := by
    clear * - h_step2
    (linarith)

  have h_step4 : (5 * x : ℝ) = (20 : ℝ) := by
    clear * - h_step3
    simp_all only [neg_mul]
    (linarith)

  have h_step5 : x = 4 := by
    clear * - h_step4
    (linarith)

  have h_step6 : a 1 = (2 * 4 - 3 : ℝ) := by
    clear * - h_step5 h₂
    simp_all only

  have h_step7 : a 1 = (5 : ℝ) := by
    clear * - h_step6
    simp_all only
    (linarith)

  have h_step8 : a 2 = (5 * 4 - 11 : ℝ) := by
    clear * - h_step5 h₃
    simp_all only

  have h_step9 : a 2 = (9 : ℝ) := by
    clear * - h_step8
    simp_all only
    (linarith)

  have h_step10 : a 2 - a 1 = (4 : ℝ) := by
    clear * - h_step7 h_step9
    simp_all only
    (linarith)

  have h_step13 : a n = a 1 + (((n : ℝ) - 1) * (a 2 - a 1 : ℝ)) := by
    clear * - h₁ h_step10
    induction' n using Nat.twoStepInduction with n IH
    · norm_num <;> linarith [h₁ 0, h₁ 1]
    · norm_num <;> linarith [h_step10]
    · norm_num [sub_eq_iff_eq_add] at * <;> linarith [h₁ n, h₁ (n + 1)]

  have h_step14 : (2009 : ℝ) = (5 : ℝ) + (((n : ℝ) - 1) * (4 : ℝ)) := by
    clear * - h_step13 h₅ h_step7 h_step10
    simp_all only

  have h_step15 : (2004 : ℝ) = ((n : ℝ) - 1) * (4 : ℝ) := by
    clear * - h_step14
    (linarith)

  have h_step16 : (501 : ℝ) = (n : ℝ) - 1 := by
    clear * - h_step15
    (linarith)

  have h_step17 : (n : ℝ) = (502 : ℝ) := by
    clear * - h_step16
    (linarith)

  have h_final : n = 502 := by
    clear * - h_step17
    exact mod_cast h_step17

  exact h_final
