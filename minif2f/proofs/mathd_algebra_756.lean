import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  have h₂ : (32 : ℝ) = (2 : ℝ) ^ 5 := by
    clear * -
    (ring)

  have h₃ : a = 5 := by
    clear * - h₀ h₂
    simp_all only
    have ha := congr_arg Real.log h₀
    simp_all only [Real.log_pow, Nat.cast_ofNat]
    apply_fun Real.log at h₀
    simp_all only [Real.log_pow, Nat.cast_ofNat]
    field_simp [Real.log_rpow zero_lt_two] at h₀
    exact h₀.elim (fun h ↦ h) <| by norm_num

  have h₅ : (5 : ℝ) ^ b = 125 := by
    clear * - h₁ h₃
    subst h₃
    simp_all only

  have h₆ : (125 : ℝ) = (5 : ℝ) ^ 3 := by
    clear * -
    (ring)

  have h₇ : b = 3 := by
    clear * - h₅ h₆
    simp_all only
    apply_fun fun x => Real.log x at h₅
    simp_all only [Real.log_pow, Nat.cast_ofNat]
    simp [Real.log_rpow, mul_comm] at h₅
    exact h₅.resolve_right (by norm_num)

  have h₈ : b ^ a = (3 : ℝ) ^ 5 := by
    clear * - h₃ h₇
    subst h₃ h₇
    (nlinarith)

  have h₉ : (3 : ℝ) ^ 5 = 243 := by
    clear * -
    (ring)

  have h₁₀ : b ^ a = 243 := by
    clear * - h₈ h₉
    simp_all only

  exact h₁₀