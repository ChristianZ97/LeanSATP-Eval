import Mathlib
open BigOperators Real Nat Topology Rat
/-- Determine the remainder of 194 (mod 11). Show that it is 7.-/

theorem mathd_numbertheory_66 : 194 % 11 = 7 := by

    simp_all only [reduceMod]