import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_618 (n : ℕ) (hn : n > 0) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n := by
  simp_all only [gt_iff_lt]
  by_contra hr
  simp_all only [not_le]
  interval_cases n <;> simp_all [pow_two, Nat.gcd_eq_iff]