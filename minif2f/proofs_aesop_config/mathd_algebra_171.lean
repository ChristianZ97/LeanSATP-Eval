import Mathlib
open BigOperators Real Nat Topology Rat
/-- Consider the function $f(x)=5x+4$.  What is $f(1)$? Show that it is 9.-/

theorem mathd_algebra_171 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 4) : f 1 = 9 := by

    aesop (config := {
    maxNormIterations       := 120
  })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))