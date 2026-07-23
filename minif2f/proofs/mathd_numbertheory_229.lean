import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- What is the remainder when $5^{30}$ is divided by 7? Show that it is 1.-/

theorem mathd_numbertheory_229 : 5 ^ 30 % 7 = 1 := by

  simp_all only [reducePow, reduceMod]
