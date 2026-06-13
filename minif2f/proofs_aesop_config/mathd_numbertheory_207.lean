import Mathlib
open BigOperators Real Nat Topology Rat
/-- Convert $852_9$ to base 10. Show that it is 695.-/

theorem mathd_numbertheory_207 : 8 * 9 ^ 2 + 5 * 9 + 2 = 695 := by

    aesop (config := {
    maxNormIterations       := 140
  })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply mul_self_le_mul_self | rw [mul_self_le_mul_self] | simp only [mul_self_le_mul_self]))
    (add unsafe 10% (by first | apply SchwartzMap.pow_mul_le_of_le_of_pow_mul_le | rw [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le] | simp only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
    (add unsafe 10% (by first | apply le_mul_of_one_le_left | rw [le_mul_of_one_le_left] | simp only [le_mul_of_one_le_left]))
    (add unsafe 10% (by first | apply mul_le_mul | rw [mul_le_mul] | simp only [mul_le_mul]))
    (add unsafe 10% (by first | apply mul_le_mul_left | rw [mul_le_mul_left] | simp only [mul_le_mul_left]))
    (add unsafe 10% (by first | apply mul_le_mul_of_nonneg_left | rw [mul_le_mul_of_nonneg_left] | simp only [mul_le_mul_of_nonneg_left]))
    (add unsafe 10% (by first | apply mul_le_mul_of_nonneg_right | rw [mul_le_mul_of_nonneg_right] | simp only [mul_le_mul_of_nonneg_right]))
    (add unsafe 10% (by first | apply two_mul_le_add_sq | rw [two_mul_le_add_sq] | simp only [two_mul_le_add_sq]))