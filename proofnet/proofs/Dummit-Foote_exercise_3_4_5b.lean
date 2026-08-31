
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_3_4_5b {G : Type*} [Group G] [IsSolvable G]
  (H : Subgroup G) [Normal H] :
  IsSolvable (G ⧸ H) := by
  infer_instance