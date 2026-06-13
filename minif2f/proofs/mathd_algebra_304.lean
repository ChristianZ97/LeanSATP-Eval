import Mathlib
open BigOperators Real Nat Topology Rat
/-- Compute $91^2$ in your head. Show that it is 8281.-/

theorem mathd_algebra_304 : 91 ^ 2 = 8281 := by

  aesop
  (add safe 2 (by ring))
  (add safe 4 (by field_simp))
  (add safe 4 (by push_neg))
  (add unsafe 100% (by exfalso))
  (add unsafe 100% (by ring_nf at *))
  (add unsafe 90% (by bound))
  (add unsafe 90% (by ext))
  (add unsafe 90% (by field_simp [*] at *))
  (add unsafe 90% (by linarith))
  (add unsafe 90% (by norm_num [*] at *))
  (add unsafe 90% (by simp))
  (add unsafe 80% (by interval_cases))
  (add unsafe 80% (by omega))
  (add unsafe 70% (by nlinarith))
  (add unsafe 70% (by norm_cast at *))
  (add unsafe 70% (by positivity))
  (add unsafe 70% (by ring_nf))
  (add unsafe 30% (by first | apply QuaternionGroup.xa_sq | rw [QuaternionGroup.xa_sq] | simp only [QuaternionGroup.xa_sq]))
  (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
  (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq_eq_one_of_squarefree | rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree] | simp only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
  (add unsafe 10% (by first | apply CoxeterSystem.simple_sq | rw [CoxeterSystem.simple_sq] | simp only [CoxeterSystem.simple_sq]))
  (add unsafe 10% (by first | apply Quaternion.coe_pow | rw [Quaternion.coe_pow] | simp only [Quaternion.coe_pow]))
  (add unsafe 10% (by first | apply mul_pow | rw [mul_pow] | simp only [mul_pow]))
  (add unsafe 10% (by first | apply quadraticChar_sq_one | rw [quadraticChar_sq_one] | simp only [quadraticChar_sq_one]))
  (add unsafe 10% (by first | apply quadraticChar_sq_one' | rw [quadraticChar_sq_one'] | simp only [quadraticChar_sq_one']))