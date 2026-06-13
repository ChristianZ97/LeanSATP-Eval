import Mathlib
open BigOperators Real Nat Topology Rat
/-- Determine the remainder of 1529 (mod 6). Show that it is 5.-/

theorem mathd_numbertheory_551 : 1529 % 6 = 5 := by

    simp_all only [reduceMod]