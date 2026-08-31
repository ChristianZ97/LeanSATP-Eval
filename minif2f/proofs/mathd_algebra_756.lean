import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  have h₂ : (32 : ℝ) = (2 : ℝ) ^ 5 := by
    clear * -
    (linarith)

  have h₃ : a = 5 := by
    clear * - h₀ h₂
    have := congr_arg Real.log h₀
    simp [Real.log_rpow, h₂] at this <;> norm_num at this <;> linarith

  have h₅ : (5 : ℝ) ^ b = 125 := by
    clear * - h₁ h₃
    (bound )

  have h₆ : (125 : ℝ) = (5 : ℝ) ^ 3 := by
    clear * -
    (linarith)

  have h₇ : b = 3 := by
    clear * - h₅ h₆
    apply_fun Real.log at h₅
    simp_all [Real.log_rpow, h₆]
    exact h₅.resolve_right <| by norm_num

  have h₈ : b ^ a = (3 : ℝ) ^ 5 := by
    clear * - h₃ h₇
    simp_all only [rpow_ofNat]

  have h₉ : (3 : ℝ) ^ 5 = 243 := by
    clear * -
    (linarith)

  have h₁₀ : b ^ a = 243 := by
    clear * - h₈ h₉
    (ring)
    (nlinarith)

  exact h₁₀
