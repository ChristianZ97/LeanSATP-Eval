import Mathlib
open BigOperators Real Nat Topology Rat
/-- What is the units digit of $2^{2010}$? Show that it is 4.-/

theorem mathd_numbertheory_175 : 2 ^ 2010 % 10 = 4 := by

    (ring)