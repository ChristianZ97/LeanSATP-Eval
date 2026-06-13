import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by
  have h_step_1 : n * 40 = Nat.gcd n 40 * Nat.lcm n 40 := by
    clear * -
    simp [Nat.gcd_mul_lcm]

  have h_step_2 : n * 40 = 10 * 280 := by
    clear * - h₁ h₂ h_step_1
    simp_all only [reduceMul]

  have h_step_3 : 10 * 280 = 2800 := by
    clear * -
    simp_all only [reduceMul]

  have h_step_4 : n * 40 = 2800 := by
    clear * - h_step_2 h_step_3
    simp_all only [reduceMul]

  have h_step_5 : n = (2800 : ℕ) / 40 := by
    clear * - h_step_4
    simp_all only [reduceDiv]
    (nlinarith)

  have h_step_6 : (2800 : ℕ) / 40 = 70 := by
    clear * -
    simp_all only [reduceDiv]

  have h_step_7 : n = 70 := by
    clear * - h_step_5 h_step_6
    subst h_step_5
    simp_all only [reduceDiv]

  exact h_step_7