import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- Notice that  \[35\cdot40=1400.\]Find some integer $n$ with $0\leq n<1399$ such that $n$ is the multiplicative inverse to 160 modulo 1399. Show that it is 1058.-/

theorem mathd_numbertheory_321 (n : ZMod 1399) (h₁ : n = 160⁻¹) : n = 1058 := by

  simp_all only
  (bound )
