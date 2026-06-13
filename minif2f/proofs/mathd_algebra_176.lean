import Mathlib
open BigOperators Real Nat Topology Rat
/-- Expand the product $(x+1)^2 \cdot x$. Show that it is x^3 + 2x^2 + x.-/

theorem mathd_algebra_176 (x : ℝ) : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by

    (nlinarith)