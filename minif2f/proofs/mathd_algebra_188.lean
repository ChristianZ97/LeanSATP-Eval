import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- Suppose $f(x)$ is an invertible function, and suppose that $f(2)=f^{-1}(2)=4$.

What is the value of $f(f(2))$? Show that it is 2.-/

theorem mathd_algebra_188 (σ : Equiv ℝ ℝ) (h : σ.1 2 = σ.2 2) : σ.1 (σ.1 2) = 2 := by

  simp_all only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.apply_symm_apply]
