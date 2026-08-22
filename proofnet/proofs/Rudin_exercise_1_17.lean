
import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_1_17
  (n : ℕ)
  (x y : EuclideanSpace ℝ (Fin n)) -- R^n
  : ‖x + y‖^2 + ‖x - y‖^2 = 2*‖x‖^2 + 2*‖y‖^2 := by
  simp [norm_add_sq_real, norm_sub_sq_real]
  ring