import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? Show that it is \dfrac{3}{7}.-/

theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by

  simp_all only [ne_eq, one_div]
  (grind only [one_div])
