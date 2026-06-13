import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
  obtain ⟨m, rfl⟩ := h₁
  obtain ⟨k, hk⟩ := h₂
  by_contra hm
  simp_all only [not_le]
  have : k < 4 := by nlinarith [sq_nonneg (k ^ 2)]
  interval_cases k <;>
    all_goals
      have : m < 8 := by nlinarith
      interval_cases m <;> omega