import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_314 (r n : ℕ) (h₀ : r = 1342 % 13) (h₁ : 0 < n) (h₂ : 1342 ∣ n)
    (h₃ : n % 13 < r) : 6710 ≤ n := by
  simp_all only [reduceMod]
  by_contra h₄
  simp_all only [not_le]
  obtain ⟨k, rfl⟩ := h₂
  simp_all only [ofNat_pos, mul_pos_iff_of_pos_left]
  on_goal 1 =>
    have : k < 5 := by nlinarith
    interval_cases k <;> simp_all