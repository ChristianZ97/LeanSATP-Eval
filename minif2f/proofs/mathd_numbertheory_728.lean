import Mathlib
open BigOperators Real Nat Topology Rat
/-- Compute $29^{13} - 5^{13}$ modulo 7. Show that it is 3.-/

theorem mathd_numbertheory_728 : (29 ^ 13 - 5 ^ 13) % 7 = 3 := by

    simp_all only [reducePow, reduceSub, reduceMod]