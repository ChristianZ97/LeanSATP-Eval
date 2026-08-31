import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- Solve  \[\frac{x-9}{x+1}=2\]for $x$. Show that it is -11.-/

theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by

  simp_all only [ne_eq]
  (grind only [div_eq_one])
