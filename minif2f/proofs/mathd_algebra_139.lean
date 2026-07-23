import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- If $a \star b = \dfrac{\left(\dfrac{1}{b} - \dfrac{1}{a}\right)}{(a - b)}$, express $3 \star 11$ as a common fraction. Show that it is \frac{1}{33}.-/

theorem mathd_algebra_139 (s : ℝ → ℝ → ℝ)
    (h₀ : ∀ (x) (_ : x ≠ 0), ∀ (y) (_ : y ≠ 0), s x y = (1 / y - 1 / x) / (x - y)) :
    s 3 11 = 1 / 33 := by

  simp_all only [ne_eq, one_div, OfNat.ofNat_ne_zero, not_false_eq_true]
  (linarith)
