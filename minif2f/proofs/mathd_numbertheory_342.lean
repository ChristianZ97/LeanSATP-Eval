import Mathlib
open BigOperators Real Nat Topology Rat
/-- Determine the remainder of 54 (mod 6). Show that it is 0.-/

theorem mathd_numbertheory_342 : 54 % 6 = 0 := by

    simp_all only [reduceMod]