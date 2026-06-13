import Mathlib
open BigOperators Real Nat Topology Rat
/-- What is the remainder when $129^{34}+96^{38}$ is divided by $11$? Show that it is 9.-/

theorem mathd_numbertheory_769 : (129 ^ 34 + 96 ^ 38) % 11 = 9 := by

    simp_all only [reducePow, reduceAdd, reduceMod]