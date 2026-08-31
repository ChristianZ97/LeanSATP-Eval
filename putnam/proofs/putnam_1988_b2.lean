
import Mathlib

open Set Filter Topology

set_option maxHeartbeats 0

abbrev putnam_1988_b2_solution : Prop := ∀ x y : ℝ, y ≥ 0 → y * (y + 1) ≤ (x + 1) ^ 2 → y * (y - 1) ≤ x ^ 2
theorem putnam_1988_b2
: (∀ x y : ℝ, (y ≥ 0 ∧ y * (y + 1) ≤ (x + 1) ^ 2) → (y * (y - 1) ≤ x ^ 2)) ↔ putnam_1988_b2_solution := by
  constructor
  · -- Prove the forward direction: LHS implies RHS
    intro h
    intro x y hy_nonneg hy_ineq
    have h_main : y * (y - 1) ≤ x ^ 2 := by
      apply h
      exact ⟨hy_nonneg, hy_ineq⟩

    exact h_main

  · -- Prove the reverse direction: RHS implies LHS
    intro h
    intro x y h_pair
    let hy_nonneg := h_pair.1
    let hy_ineq := h_pair.2
    have h_main : y * (y - 1) ≤ x ^ 2 := by
      apply h
      exact hy_nonneg
      exact hy_ineq

    exact h_main