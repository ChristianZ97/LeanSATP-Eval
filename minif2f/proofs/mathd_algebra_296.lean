import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- A $3491$ by $3491$ square has its length decreased by $60$ and its width increased by $60$.  By how much does its area change? Show that it is 3600.-/

theorem mathd_algebra_296 : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by

  simp only [Int.reduceSub, Int.reduceAdd, Int.reduceMul, Int.reducePow, abs_neg, abs_ofNat] at *
