import Mathlib
open BigOperators Real Nat Topology Rat
/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? Show that it is \dfrac{3}{7}.-/

theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by

    simp_all only [ne_eq, one_div]
    (field_simp)
    (norm_num [*] at *)