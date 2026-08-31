
import Mathlib

open Topology Filter Polynomial

set_option maxHeartbeats 0

abbrev putnam_1963_b3_solution : Set (ℝ → ℝ) := {f | ContDiff ℝ 1 f ∧ Differentiable ℝ (deriv f) ∧
      (∀ x y : ℝ, (f x) ^ 2 - (f y) ^ 2 = f (x + y) * f (x - y))}
theorem putnam_1963_b3
    (f : ℝ → ℝ) :
    f ∈ putnam_1963_b3_solution ↔
      (ContDiff ℝ 1 f ∧ Differentiable ℝ (deriv f) ∧
      ∀ x y : ℝ, (f x) ^ 2 - (f y) ^ 2 = f (x + y) * f (x - y)) := by
  constructor
  · intro h
    simp only [Set.mem_setOf_eq] at h
    exact h

  · intro h
    simp only [Set.mem_setOf_eq]
    exact h