import Mathlib
open BigOperators Real Nat Topology Rat
/-- Assuming $x\ne0$, simplify $\frac{12}{x \cdot x} \cdot \frac{x^4}{14x}\cdot \frac{35}{3x}$. Show that it is 10.-/

theorem mathd_algebra_441 (x : ℝ) (h₀ : x ≠ 0) :
    12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by

    simp_all only [ne_eq]
    (field_simp)
    (nlinarith)