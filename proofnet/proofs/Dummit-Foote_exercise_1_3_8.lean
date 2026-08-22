
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_1_3_8 : Infinite (Equiv.Perm ℕ) := by
  inhabit ℕ
  infer_instance