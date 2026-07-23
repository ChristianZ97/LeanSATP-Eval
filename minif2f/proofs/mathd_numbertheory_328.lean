import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- What is the remainder when 5 to the 999,999th power is divided by 7? Show that it is 6.-/

theorem mathd_numbertheory_328 : 5 ^ 999999 % 7 = 6 := by

  (omega)
