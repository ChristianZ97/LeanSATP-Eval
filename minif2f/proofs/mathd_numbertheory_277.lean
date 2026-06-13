import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_277 (m n : ℕ) (h₀ : Nat.gcd m n = 6) (h₁ : Nat.lcm m n = 126) :
  60 ≤ m + n := by
  have aux := Nat.gcd_mul_lcm m n
  simp_all only [reduceMul, ge_iff_le]
  by_contra res
  simp_all only [not_le]
  on_goal 1 =>
    have : m < 60 := by nlinarith
    have : n < 60 := by nlinarith
    interval_cases m <;> interval_cases n <;>
      first
      | omega
      | aesop