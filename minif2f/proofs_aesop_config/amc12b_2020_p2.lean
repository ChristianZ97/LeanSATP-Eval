import Mathlib
open BigOperators Real Nat Topology Rat
/-- What is the value of the following expression?

$\frac{100^2-7^2}{70^2-11^2} \cdot \frac{(70-11)(70+11)}{(100-7)(100+7)}$

$\textbf{(A) } 1 \qquad \textbf{(B) } \frac{9951}{9950} \qquad \textbf{(C) } \frac{4780}{4779} \qquad \textbf{(D) } \frac{108}{107} \qquad \textbf{(E) } \frac{81}{80} $ Show that it is \textbf{(A) } 1.-/

theorem amc12b_2020_p2 :
    (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) =
      1 := by

    aesop (config := {
    maxGoals                := 64
  })
    (add safe 1 (by norm_num))
    (add safe 2 (by field_simp))
    (add safe 2 (by ring))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by exfalso))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 30% (by first | apply WeierstrassCurve.ψ_one | rw [WeierstrassCurve.ψ_one] | simp only [WeierstrassCurve.ψ_one]))
    (add unsafe 20% (by first | apply DualNumber.snd_eps | rw [DualNumber.snd_eps] | simp only [DualNumber.snd_eps]))
    (add unsafe 10% (by first | apply WeierstrassCurve.Jacobian.smul_fin3 | rw [WeierstrassCurve.Jacobian.smul_fin3] | simp only [WeierstrassCurve.Jacobian.smul_fin3]))