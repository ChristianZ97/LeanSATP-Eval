import Mathlib
open BigOperators Real Nat Topology Rat
/-- Find the units digit of $29 \cdot 79 + 31 \cdot 81$. Show that it is 2.-/

theorem mathd_numbertheory_235 : (29 * 79 + 31 * 81) % 10 = 2 := by

    simp_all only [reduceMul, reduceAdd, reduceMod]