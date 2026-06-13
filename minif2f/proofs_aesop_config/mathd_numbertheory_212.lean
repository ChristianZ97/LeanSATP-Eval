import Mathlib
open BigOperators Real Nat Topology Rat
/-- Find the units digit of $16^{17} \times 17^{18} \times 18^{19}$. Show that it is 8.-/

theorem mathd_numbertheory_212 : 16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10 = 8 := by

    aesop (config := {
    maxGoals                := 64
  })
    (add safe 1 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by exfalso))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply ENNReal.continuousAt_mul_const | rw [ENNReal.continuousAt_mul_const] | simp only [ENNReal.continuousAt_mul_const]))