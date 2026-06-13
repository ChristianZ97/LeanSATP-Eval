import Mathlib
open BigOperators Real Nat Topology Rat
/-- If $\left(\sqrt[4]{11}\right)^{3x-3}=\frac{1}{5}$, what is the value of $\left(\sqrt[4]{11}\right)^{6x+2}$? Express your answer as a fraction. Show that it is \frac{121}{25}.-/

theorem mathd_algebra_275 (x : ℝ) (h : ((11 : ℝ) ^ (1 / 4)) ^ (3 * x - 3) = 1 / 5) :
    ((11 : ℝ) ^ (1 / 4)) ^ (6 * x + 2) = 121 / 25 := by

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
    (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))