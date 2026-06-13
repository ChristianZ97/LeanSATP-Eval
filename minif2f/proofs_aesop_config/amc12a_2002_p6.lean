import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12a_2002_p6 (n : ℕ) (h₀ : 0 < n) : ∃ m, m > n ∧ ∃ p, m * p ≤ m + p := by
  simp_all only [gt_iff_lt]
  set m := n + 2
  refine ⟨m, ?_, 1, ?_⟩ <;> simp [m, h₀]