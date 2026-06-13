import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
  intro h_eq

  have h_2003_mod : (2003 : ℤ) % 7 = 1 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 2 (by ring))
    (add safe 2 (by zify))
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by nlinarith))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply Nat.odd_iff | rw [Nat.odd_iff] | simp only [Nat.odd_iff]))
    (add unsafe 30% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 30% (by first | apply Nat.mul_mod | rw [Nat.mul_mod] | simp only [Nat.mul_mod]))
    (add unsafe 30% (by first | apply Nat.mul_mod_left | rw [Nat.mul_mod_left] | simp only [Nat.mul_mod_left]))
    (add unsafe 20% (by first | apply Nat.even_iff | rw [Nat.even_iff] | simp only [Nat.even_iff]))

  have h_eq_cong : (4 * x ^ 3 - 7 * y ^ 3) % 7 = (2003 : ℤ) % 7 := by
    clear * - h_eq
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

  have h_7y_div : (7 * y ^ 3) % 7 = 0 := by
    clear * -
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

  have h_lhs_cong : (4 * x ^ 3) % 7 = (4 * x ^ 3 - 7 * y ^ 3) % 7 := by
    clear * - h_7y_div
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
    (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_4x_cong : (4 * x ^ 3) % 7 = 1 := by
    clear * - h_eq_cong h_lhs_cong h_2003_mod
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
    (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_mult_2_left : (2 * (4 * x ^ 3)) % 7 = (2 * 1 : ℤ) % 7 := by
    clear * - h_4x_cong
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

  have h_8_mod_7 : (8 : ℤ) % 7 = 1 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 2 (by ring))
    (add safe 2 (by zify))
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 30% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 30% (by first | apply Nat.even_iff | rw [Nat.even_iff] | simp only [Nat.even_iff]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 20% (by first | apply Int.mul_emod | rw [Int.mul_emod] | simp only [Int.mul_emod]))
    (add unsafe 20% (by first | apply Int.odd_iff | rw [Int.odd_iff] | simp only [Int.odd_iff]))
    (add unsafe 20% (by first | apply Nat.mul_mod_left | rw [Nat.mul_mod_left] | simp only [Nat.mul_mod_left]))

  have h_x_cubed_cong : (x ^ 3) % 7 = 2 := by
    clear * - h_mult_2_left h_8_mod_7
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
    (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_case_0 : (0 : ℤ) ^ 3 % 7 = 0 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    enableUnfold            := false
    })
    (add safe 1 (by norm_num))
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 10% (by first | apply LucasLehmer.s | rw [LucasLehmer.s] | simp only [LucasLehmer.s]))
    (add unsafe 10% (by first | apply MulZeroClass | rw [MulZeroClass] | simp only [MulZeroClass]))
    (add unsafe 10% (by first | apply QuaternionAlgebra.natCast_imI | rw [QuaternionAlgebra.natCast_imI] | simp only [QuaternionAlgebra.natCast_imI]))
    (add unsafe 10% (by first | apply WeierstrassCurve.Jacobian.smul_fin3 | rw [WeierstrassCurve.Jacobian.smul_fin3] | simp only [WeierstrassCurve.Jacobian.smul_fin3]))
    (add unsafe 10% (by first | apply legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero | rw [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero] | simp only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
    (add unsafe 10% (by first | apply zero_pow | rw [zero_pow] | simp only [zero_pow]))

  have h_case_1 : (1 : ℤ) ^ 3 % 7 = 1 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 2 (by field_simp))
    (add safe 2 (by ring))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 30% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 30% (by first | apply Int.mul_emod | rw [Int.mul_emod] | simp only [Int.mul_emod]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 30% (by first | apply neg_one_pow_eq_pow_mod_two | rw [neg_one_pow_eq_pow_mod_two] | simp only [neg_one_pow_eq_pow_mod_two]))
    (add unsafe 20% (by first | apply Int.emod_emod | rw [Int.emod_emod] | simp only [Int.emod_emod]))

  have h_case_2 : (2 : ℤ) ^ 3 % 7 = 1 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 1 (by ring))
    (add safe 2 (by zify))
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 40% (by first | apply Nat.even_iff | rw [Nat.even_iff] | simp only [Nat.even_iff]))
    (add unsafe 40% (by first | apply Nat.odd_iff | rw [Nat.odd_iff] | simp only [Nat.odd_iff]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 30% (by first | apply Nat.mul_mod | rw [Nat.mul_mod] | simp only [Nat.mul_mod]))
    (add unsafe 30% (by first | apply Nat.mul_mod_left | rw [Nat.mul_mod_left] | simp only [Nat.mul_mod_left]))
    (add unsafe 30% (by first | apply neg_one_pow_eq_pow_mod_two | rw [neg_one_pow_eq_pow_mod_two] | simp only [neg_one_pow_eq_pow_mod_two]))

  have h_case_3 : (3 : ℤ) ^ 3 % 7 = 6 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 40% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 40% (by first | apply Nat.pow_mod | rw [Nat.pow_mod] | simp only [Nat.pow_mod]))
    (add unsafe 30% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 30% (by first | apply Int.mul_emod | rw [Int.mul_emod] | simp only [Int.mul_emod]))
    (add unsafe 30% (by first | apply neg_one_pow_eq_pow_mod_two | rw [neg_one_pow_eq_pow_mod_two] | simp only [neg_one_pow_eq_pow_mod_two]))

  have h_case_4 : (4 : ℤ) ^ 3 % 7 = 1 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 2 (by ring))
    (add safe 2 (by zify))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply Int.odd_iff | rw [Int.odd_iff] | simp only [Int.odd_iff]))
    (add unsafe 40% (by first | apply Nat.even_iff | rw [Nat.even_iff] | simp only [Nat.even_iff]))
    (add unsafe 30% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 30% (by first | apply Int.mul_emod | rw [Int.mul_emod] | simp only [Int.mul_emod]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))

  have h_case_5 : (5 : ℤ) ^ 3 % 7 = 6 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 1 (by ring))
    (add safe 2 (by zify))
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply Nat.mul_mod | rw [Nat.mul_mod] | simp only [Nat.mul_mod]))
    (add unsafe 40% (by first | apply Nat.mul_mod_left | rw [Nat.mul_mod_left] | simp only [Nat.mul_mod_left]))
    (add unsafe 40% (by first | apply neg_one_pow_eq_pow_mod_two | rw [neg_one_pow_eq_pow_mod_two] | simp only [neg_one_pow_eq_pow_mod_two]))
    (add unsafe 30% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 30% (by first | apply Int.mul_emod | rw [Int.mul_emod] | simp only [Int.mul_emod]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 30% (by first | apply Nat.pow_mod | rw [Nat.pow_mod] | simp only [Nat.pow_mod]))

  have h_case_6 : (6 : ℤ) ^ 3 % 7 = 6 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 2 (by ring))
    (add safe 2 (by zify))
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply Int.odd_iff | rw [Int.odd_iff] | simp only [Int.odd_iff]))
    (add unsafe 40% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 40% (by first | apply Nat.pow_mod | rw [Nat.pow_mod] | simp only [Nat.pow_mod]))
    (add unsafe 30% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 30% (by first | apply Int.mul_emod | rw [Int.mul_emod] | simp only [Int.mul_emod]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 20% (by first | apply Int.emod_emod | rw [Int.emod_emod] | simp only [Int.emod_emod]))

  have h_residue_set : (x ^ 3) % 7 = 0 ∨ (x ^ 3) % 7 = 1 ∨ (x ^ 3) % 7 = 6 := by
    clear * - h_case_0 h_case_1 h_case_2 h_case_3 h_case_4 h_case_5 h_case_6
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, EuclideanDomain.zero_mod, one_pow,
      Int.reduceMod, Int.reducePow, EuclideanDomain.mod_eq_zero]
    have h1 : x ^ 3 % 7 = (x % 7) ^ 3 % 7
    · simp [pow_succ, Int.mul_emod, Int.ModEq]
    · simp_all only
      have h2 := Int.emod_nonneg x (by decide : (7 : ℤ) ≠ 0)
      have h3 : x % 7 < 7 := Int.emod_lt _ (by norm_num)
      interval_cases h : x % 7 <;> simp_all (config := { decide := true })

  have h_2_not_0 : (2 : ℤ) ≠ 0 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    enableUnfold            := false
    })
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by exfalso))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply LucasLehmer.mersenne_int_ne_zero | rw [LucasLehmer.mersenne_int_ne_zero] | simp only [LucasLehmer.mersenne_int_ne_zero]))
    (add unsafe 40% (by first | apply Nat.prime_two | rw [Nat.prime_two] | simp only [Nat.prime_two]))
    (add unsafe 40% (by first | apply zero_lt_two | rw [zero_lt_two] | simp only [zero_lt_two]))
    (add unsafe 10% (by first | apply Nat.cast_ofNat | rw [Nat.cast_ofNat] | simp only [Nat.cast_ofNat]))
    (add unsafe 10% (by first | apply Nat.cast_two | rw [Nat.cast_two] | simp only [Nat.cast_two]))

  have h_2_not_1 : (2 : ℤ) ≠ 1 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by exfalso))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 40% (by first | apply Nat.Prime.ne_one | rw [Nat.Prime.ne_one] | simp only [Nat.Prime.ne_one]))
    (add unsafe 40% (by first | apply Set.ncard_eq_two | rw [Set.ncard_eq_two] | simp only [Set.ncard_eq_two]))
    (add unsafe 30% (by first | apply Nat.prime_two | rw [Nat.prime_two] | simp only [Nat.prime_two]))
    (add unsafe 30% (by first | apply Nat.two_mul | rw [Nat.two_mul] | simp only [Nat.two_mul]))
    (add unsafe 10% (by first | apply Nat.cast_two | rw [Nat.cast_two] | simp only [Nat.cast_two]))
    (add unsafe 10% (by first | apply even_iff_two_dvd | rw [even_iff_two_dvd] | simp only [even_iff_two_dvd]))

  have h_2_not_6 : (2 : ℤ) ≠ 6 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    enableUnfold            := false
    })
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 40% (by first | apply Nat.factorial_two | rw [Nat.factorial_two] | simp only [Nat.factorial_two]))
    (add unsafe 40% (by first | apply Nat.prime_two | rw [Nat.prime_two] | simp only [Nat.prime_two]))
    (add unsafe 10% (by first | apply Nat.cast_two | rw [Nat.cast_two] | simp only [Nat.cast_two]))
    (add unsafe 10% (by first | apply summable_condensed_iff_of_nonneg | rw [summable_condensed_iff_of_nonneg] | simp only [summable_condensed_iff_of_nonneg]))
    (add unsafe 10% (by first | apply zero_lt_two | rw [zero_lt_two] | simp only [zero_lt_two]))

  have h_false : False := by
    clear * - h_x_cubed_cong h_residue_set h_2_not_0 h_2_not_1 h_2_not_6
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
    (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  exact h_false
