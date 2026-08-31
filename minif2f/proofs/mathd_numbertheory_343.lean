import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- What is the units digit of the product of all of the odd integers between 0 and 12? Show that it is 5.-/

theorem mathd_numbertheory_343 : (∏ k in Finset.range 6, (2 * k + 1)) % 10 = 5 := by

  (bound )
