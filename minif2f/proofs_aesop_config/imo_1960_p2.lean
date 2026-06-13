import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem imo_1960_p2 (x : ℝ) (h₀ : 0 ≤ 1 + 2 * x) (h₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0)
    (h₂ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9) : -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, one_div]
  apply And.intro
  · norm_num1 at h₀ ⊢ <;> nlinarith
  · rw [div_lt_iff (by positivity)] at h₂
    nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (by linarith : 0 ≤ 1 + 2 * x),
      mul_nonneg (Real.sqrt_nonneg (1 + 2 * x)) (sub_nonneg.2 h₀)]