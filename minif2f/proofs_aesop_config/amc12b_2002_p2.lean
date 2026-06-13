import Mathlib
open BigOperators Real Nat Topology Rat
/-- What is the value of  $(3x - 2)(4x + 1) - (3x - 2)4x + 1$ when $x=4$?

$\mathrm{(A)}\ 0
\qquad\mathrm{(B)}\ 1
\qquad\mathrm{(C)}\ 10
\qquad\mathrm{(D)}\ 11
\qquad\mathrm{(E)}\ 12$ Show that it is \mathrm{(D)}\ 11.-/

theorem amc12b_2002_p2 (x : ℤ) (h₀ : x = 4) :
    (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11 := by

    aesop (config := {
    maxNormIterations       := 120
  })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))