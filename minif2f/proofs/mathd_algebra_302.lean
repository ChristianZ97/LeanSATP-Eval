import Mathlib
open BigOperators Real Nat Topology Rat
/-- Evaluate $\left(\frac{i}{2}\right)^2$. Show that it is -\frac{1}{4}.-/

theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by

    simp_all only [one_div]
    (ring)
    simp_all only [Complex.I_sq, one_div, neg_mul, one_mul]
    (ring)