
import Mathlib

open Filter Topology Nat

set_option maxHeartbeats 0

abbrev putnam_1990_a5_solution : Prop := ∀ n ≥ 1, ∀ A B : Matrix (Fin n) (Fin n) ℝ,
    A * B * A * B = 0 → B * A * B * A = 0
theorem putnam_1990_a5 :
  putnam_1990_a5_solution ↔
  (∀ n ≥ 1, ∀ A B : Matrix (Fin n) (Fin n) ℝ,
    A * B * A * B = 0 → B * A * B * A = 0) := by
  constructor
  · intro h
    exact h

  · intro h
    exact h