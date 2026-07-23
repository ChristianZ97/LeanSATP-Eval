import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- Find the modulo 4 residue of $121 \cdot 122 \cdot 123$. Show that it is 2.-/

theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by

  simp_all only [reduceMul, reduceMod]
