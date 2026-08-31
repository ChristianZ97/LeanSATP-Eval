import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  have h_step3 : s = (9:ℝ) - (2:ℝ) * ((3:ℝ) * s + (1:ℝ)) := by
    clear * - h₀ h₁
    (linarith)

  have h_step4 : s = (9:ℝ) - (6:ℝ) * s - (2:ℝ) := by
    clear * - h_step3
    (linarith)

  have h_step5 : s = (7:ℝ) - (6:ℝ) * s := by
    clear * - h_step4
    (linarith)

  have h_step6 : s + (6:ℝ) * s = (7:ℝ) := by
    clear * - h_step5
    (linarith)

  have h_step7 : (7:ℝ) * s = (7:ℝ) := by
    clear * - h_step6
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀]
    (linarith)

  have h_step8 : s = (1:ℝ) := by
    clear * - h_step7
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀]

  have h_step9 : t = (3:ℝ) * (1:ℝ) + (1:ℝ) := by
    clear * - h₁ h_step8
    simp_all only [mul_one]

  have h_step10 : t = (3:ℝ) + (1:ℝ) := by
    clear * - h_step9
    simp_all only [mul_one]

  have h_step11 : t = (4:ℝ) := by
    clear * - h_step10
    simp_all only
    (linarith)

  exact ⟨h_step8, h_step11⟩
