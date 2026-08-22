import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


theorem exercise_1_1_20 {G : Type*} [Group G] {x : G} :
  orderOf x = orderOf x⁻¹ := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by simp))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [orderOf_inv]))
    (add norm 0 (by grind only [DihedralGroup.orderOf_r_one]))
    (add norm 0 (by grind only [orderOf_neg_one]))
    (add norm 0 (by grind only [orderOf_eq_prime]))
    (add norm 0 (by grind only [inv_eq_iff_eq_inv]))
    (add norm 0 (by grind only [inv_eq_self_of_orderOf_eq_two]))
    (add norm 0 (by grind only [Subgroup.orderOf_coe]))
    (add norm 0 (by grind only [orderOf_eq_orderOf_iff]))
    (add norm 0 (by grind only [QuaternionGroup.orderOf_a_one]))
    (add norm 0 (by grind only [pow_orderOf_eq_one]))
    (add norm 0 (by grind only [IsPrimitiveRoot.eq_orderOf]))
    (add norm 0 (by grind only [orderOf_eq_one_iff]))
    (add norm 0 (by grind only [QuaternionGroup.orderOf_xa]))
    (add norm 0 (by grind only [orderOf]))
    (add norm 0 (by grind only [MonoidHom.FixedPointFree.orderOf_ne_two_of_involutive]))
    (add norm 0 (by grind only [DihedralGroup.orderOf_r]))
    (add norm 0 (by grind only [orderOf_dvd_of_pow_eq_one]))
    (add norm 0 (by grind only [orderOf_le_of_pow_eq_one]))
    (add norm 0 (by grind only [orderOf_submonoid]))
    (add norm 0 (by grind only [orderOf_eq_prime_pow]))
    (add norm 0 (by grind only [orderOf_dvd_iff_pow_eq_one]))
    (add norm 0 (by grind only [DihedralGroup.orderOf_sr]))
    (add norm 0 (by grind only [MulAction.period_dvd_orderOf]))
    (add norm 0 (by grind only [orderOf_units]))
    (add norm 0 (by grind only [orderOf_eq_iff]))
    (add norm 0 (by grind only [QuaternionGroup.orderOf_a]))
    (add norm 0 (by grind only [inv_inj]))
    (add norm 0 (by grind only [orderOf_dvd_of_mem_zpowers]))
    (add norm 0 (by grind only [orderOf_one]))
    (add norm 0 (by grind only [orderOf_pos]))
    (add unsafe 50% (by nlinarith [inv_eq_iff_mul_eq_one]))
    (add unsafe 50% (by nlinarith [mul_eq_one_iff_eq_inv]))
