import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


theorem exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    maxGoals := 512
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [mul_left_comm]))
    (add norm 0 (by grind only [mul_assoc]))
    (add norm 0 (by grind only [mul_right_comm]))
    (add norm 0 (by grind only [mul_comm]))
    (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
    (add norm 0 (by grind only [Zsqrtd.smul_val]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
    (add norm 0 (by grind only [Nat.cast_mul]))
    (add norm 0 (by grind only [Pell.xz]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [IsMulCentral]))
    (add norm 0 (by grind only [mul_mul_mul_comm]))
    (add norm 0 (by grind only [QuaternionAlgebra.coe_commutes]))
    (add norm 0 (by rw [ZMod.natCast_self]))
    (add norm 0 (by rw [ZMod.natCast_zmod_val]))
    (add norm 0 (by grind only [AddChar.mulShift_apply]))
    (add norm 0 (by grind only [ZNum.cast_mul]))
    (add norm 0 (by grind only [Pell.yz]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imK]))
    (add norm 0 (by rw [Quaternion.coe_commutes]))
    (add norm 0 (by grind only [gaussSum]))
    (add norm 0 (by grind only [AddChar.mulShift_mul]))
    (add norm 0 (by rw [ZMod.natCast_val]))
    (add norm 0 (by grind only [AddChar.map_add_eq_mul]))
    (add norm 0 (by grind only [Pell.isPell_norm]))
    (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_pow_mul_iff]))
    (add norm 0 (by grind only [Pell.d]))
    (add norm 0 (by grind only [gaussSum_mulShift]))
    (add norm 0 (by grind only [LucasLehmer.X.coe_mul]))
    (add norm 0 (by grind only [Pell.dz_val]))
    (add norm 0 (by grind only [ZNum.mul_to_int]))
