import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- What is the modulo $6$ remainder of the sum $1+2+3+4+\dots+98+99+100?$ Show that it is 4.-/

theorem mathd_numbertheory_237 : (∑ k in Finset.range 101, k) % 6 = 4 := by

  (bound )
