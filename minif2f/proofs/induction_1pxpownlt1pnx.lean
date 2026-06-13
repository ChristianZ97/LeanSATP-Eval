import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  induction' h₁ with r hr
  · simp_all only [succ_eq_add_one, zero_add, Nat.cast_one, one_mul, pow_one, le_refl]
  · simp_all only [succ_eq_add_one, zero_add, le_eq, Nat.cast_add, Nat.cast_one]
    rw [pow_succ, mul_comm]
    nlinarith [sq_nonneg x, pow_pos (sub_pos.mpr h₀) r]