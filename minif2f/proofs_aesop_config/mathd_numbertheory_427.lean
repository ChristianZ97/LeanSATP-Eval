import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_427 (a : ℕ) (h₀ : a = ∑ k in Nat.divisors 500, k) :
    (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = 25 := by
  have h_step_1 : 500 = 2^2 * 5^3 := by
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
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply Nat.mod_two_add_succ_mod_two | rw [Nat.mod_two_add_succ_mod_two] | simp only [Nat.mod_two_add_succ_mod_two]))
    (add unsafe 40% (by first | apply Nat.mul_mod | rw [Nat.mul_mod] | simp only [Nat.mul_mod]))
    (add unsafe 40% (by first | apply Nat.two_mul | rw [Nat.two_mul] | simp only [Nat.two_mul]))
    (add unsafe 40% (by first | apply Nat.two_mul_odd_div_two | rw [Nat.two_mul_odd_div_two] | simp only [Nat.two_mul_odd_div_two]))
    (add unsafe 10% (by first | apply Int.cast_ofNat | rw [Int.cast_ofNat] | simp only [Int.cast_ofNat]))
    (add unsafe 10% (by first | apply Nat.cast_ofNat | rw [Nat.cast_ofNat] | simp only [Nat.cast_ofNat]))
    (add unsafe 10% (by first | apply QuaternionGroup.a_mul_a | rw [QuaternionGroup.a_mul_a] | simp only [QuaternionGroup.a_mul_a]))

  have h_sigma_2_2_form : (∑ k in Nat.divisors (2^2), k) = (2^(2+1) - 1) / (2 - 1 : ℕ) := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply FiberBundle.extChartAt_target | rw [FiberBundle.extChartAt_target] | simp only [FiberBundle.extChartAt_target]))
    (add unsafe 30% (by first | apply Ideal.Quotient.mk_eq_mk_iff_sub_mem | rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] | simp only [Ideal.Quotient.mk_eq_mk_iff_sub_mem]))
    (add unsafe 30% (by first | apply MeasureTheory.setAverage_congr_fun | rw [MeasureTheory.setAverage_congr_fun] | simp only [MeasureTheory.setAverage_congr_fun]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_le_of_lt | rw [Ordinal.nadd_lt_nadd_of_le_of_lt] | simp only [Ordinal.nadd_lt_nadd_of_le_of_lt]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_lt_of_le | rw [Ordinal.nadd_lt_nadd_of_lt_of_le] | simp only [Ordinal.nadd_lt_nadd_of_lt_of_le]))
    (add unsafe 30% (by first | apply Subring.gc_map_comap | rw [Subring.gc_map_comap] | simp only [Subring.gc_map_comap]))

  have h_sigma_2_2_subst : (∑ k in Nat.divisors (2^2), k) = (2^3 - 1) / 1 := by
    clear * - h_sigma_2_2_form
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
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

  have h_sigma_2_2_eval : (∑ k in Nat.divisors (2^2), k) = (8 - 1) / 1 := by
    clear * - h_sigma_2_2_subst
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
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
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_sigma_2_2_val : (∑ k in Nat.divisors (2^2), k) = 7 := by
    clear * - h_sigma_2_2_eval
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
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
    (add unsafe 30% (by first | apply Ioo_mem_nhdsWithin_Iic | rw [Ioo_mem_nhdsWithin_Iic] | simp only [Ioo_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_sigma_5_3_form : (∑ k in Nat.divisors (5^3), k) = (5^(3+1) - 1) / (5 - 1 : ℕ) := by
    clear * -
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
    (add unsafe 100% (by split))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply CategoryTheory.Limits.prod.triangle | rw [CategoryTheory.Limits.prod.triangle] | simp only [CategoryTheory.Limits.prod.triangle]))
    (add unsafe 30% (by first | apply FiberBundle.extChartAt_target | rw [FiberBundle.extChartAt_target] | simp only [FiberBundle.extChartAt_target]))
    (add unsafe 30% (by first | apply Matrix.BlockTriangular.inv_toBlock | rw [Matrix.BlockTriangular.inv_toBlock] | simp only [Matrix.BlockTriangular.inv_toBlock]))
    (add unsafe 30% (by first | apply MulHom.prod_apply | rw [MulHom.prod_apply] | simp only [MulHom.prod_apply]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_le_of_lt | rw [Ordinal.nadd_lt_nadd_of_le_of_lt] | simp only [Ordinal.nadd_lt_nadd_of_le_of_lt]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_lt_of_le | rw [Ordinal.nadd_lt_nadd_of_lt_of_le] | simp only [Ordinal.nadd_lt_nadd_of_lt_of_le]))
    (add unsafe 30% (by first | apply Subsemigroup.bot_prod_bot | rw [Subsemigroup.bot_prod_bot] | simp only [Subsemigroup.bot_prod_bot]))
    (add unsafe 30% (by first | apply Subsemiring.gc_map_comap | rw [Subsemiring.gc_map_comap] | simp only [Subsemiring.gc_map_comap]))

  have h_sigma_5_3_subst : (∑ k in Nat.divisors (5^3), k) = (5^4 - 1) / 4 := by
    clear * - h_sigma_5_3_form
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
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

  have h_sigma_5_3_eval : (∑ k in Nat.divisors (5^3), k) = (625 - 1) / 4 := by
    clear * - h_sigma_5_3_subst
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
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
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_sigma_5_3_div : (∑ k in Nat.divisors (5^3), k) = 624 / 4 := by
    clear * - h_sigma_5_3_eval
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
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
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_sigma_5_3_val : (∑ k in Nat.divisors (5^3), k) = 156 := by
    clear * - h_sigma_5_3_div
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
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
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_coprime_4_125 : Nat.Coprime (2^2) (5^3) := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 1 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by exfalso))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply FiberBundle.extChartAt_target | rw [FiberBundle.extChartAt_target] | simp only [FiberBundle.extChartAt_target]))
    (add unsafe 30% (by first | apply Ideal.map_snd_prod | rw [Ideal.map_snd_prod] | simp only [Ideal.map_snd_prod]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Subring.gc_map_comap | rw [Subring.gc_map_comap] | simp only [Subring.gc_map_comap]))

  have h_sum_mult : (∑ k in Nat.divisors 500, k) = (∑ k in Nat.divisors (2^2), k) * (∑ k in Nat.divisors (5^3), k) := by
    clear * - h_step_1 h_coprime_4_125
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
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_prod_1092 : (∑ k in Nat.divisors (2^2), k) * (∑ k in Nat.divisors (5^3), k) = 7 * 156 := by
    clear * - h_sigma_2_2_val h_sigma_5_3_val
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
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_a_calc : a = 7 * 156 := by
    clear * - h₀ h_sum_mult h_prod_1092
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

  have h_a_val : a = 1092 := by
    clear * - h_a_calc
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

  have h_1092_1 : 1092 = 2 * 546 := by
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
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply Int.cast_two | rw [Int.cast_two] | simp only [Int.cast_two]))
    (add unsafe 40% (by first | apply Pell.eq_of_xn_modEq_lem2 | rw [Pell.eq_of_xn_modEq_lem2] | simp only [Pell.eq_of_xn_modEq_lem2]))
    (add unsafe 40% (by first | apply ack_two | rw [ack_two] | simp only [ack_two]))
    (add unsafe 30% (by first | apply Nat.two_mul | rw [Nat.two_mul] | simp only [Nat.two_mul]))

  have h_546_1 : 546 = 2 * 273 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by exfalso))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Int.cast_two | rw [Int.cast_two] | simp only [Int.cast_two]))
    (add unsafe 40% (by first | apply Quaternion.self_add_star | rw [Quaternion.self_add_star] | simp only [Quaternion.self_add_star]))
    (add unsafe 40% (by first | apply ack_two | rw [ack_two] | simp only [ack_two]))
    (add unsafe 30% (by first | apply Nat.two_mul | rw [Nat.two_mul] | simp only [Nat.two_mul]))
    (add unsafe 10% (by first | apply Nat.cast_two | rw [Nat.cast_two] | simp only [Nat.cast_two]))
    (add unsafe 10% (by first | apply two_mul | rw [two_mul] | simp only [two_mul]))

  have h_273_1 : 273 = 3 * 91 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 40% (by first | apply Int.cast_ofNat | rw [Int.cast_ofNat] | simp only [Int.cast_ofNat]))
    (add unsafe 40% (by first | apply Int.cast_two | rw [Int.cast_two] | simp only [Int.cast_two]))
    (add unsafe 40% (by first | apply Quaternion.star_add_self' | rw [Quaternion.star_add_self'] | simp only [Quaternion.star_add_self']))
    (add unsafe 40% (by first | apply ack_two | rw [ack_two] | simp only [ack_two]))
    (add unsafe 30% (by first | apply Nat.two_mul | rw [Nat.two_mul] | simp only [Nat.two_mul]))

  have h_91_1 : 91 = 7 * 13 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by exfalso))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 30% (by first | apply ArithmeticFunction.coe_zeta_mul_coe_moebius | rw [ArithmeticFunction.coe_zeta_mul_coe_moebius] | simp only [ArithmeticFunction.coe_zeta_mul_coe_moebius]))
    (add unsafe 30% (by first | apply ArithmeticFunction.moebius_mul_coe_zeta | rw [ArithmeticFunction.moebius_mul_coe_zeta] | simp only [ArithmeticFunction.moebius_mul_coe_zeta]))
    (add unsafe 10% (by first | apply ArithmeticFunction.intCoe_apply | rw [ArithmeticFunction.intCoe_apply] | simp only [ArithmeticFunction.intCoe_apply]))

  have h_factors_explicit : 1092 = 2^2 * 3 * 7 * 13 := by
    clear * - h_1092_1 h_546_1 h_273_1 h_91_1
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
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_primes_1092 : Finset.filter (fun x => Nat.Prime x) (Nat.divisors 1092) = {2, 3, 7, 13} := by
    clear * - h_factors_explicit
    simp_all only [reducePow, reduceMul]
    ext p
    simp_all only [Finset.mem_filter, mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true,
      Finset.mem_insert, Finset.mem_singleton]
    constructor <;> aesop
    · have : p ≤ 1092 := Nat.le_of_dvd (by norm_num) left
      interval_cases p <;> norm_num at *
    · use 546
    · exact Nat.prime_two
    · use 364
    · exact Nat.prime_three
    · use 156
    · exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl
    · use 84
    · decide

  have h_sum_primes_start : ∑ k in {2, 3, 7, 13}, k = 2 + 3 + 7 + 13 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Ico_mem_nhdsWithin_Iic | rw [Ico_mem_nhdsWithin_Iic] | simp only [Ico_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply Ioo_mem_nhdsWithin_Iic | rw [Ioo_mem_nhdsWithin_Iic] | simp only [Ioo_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_sum_primes_add1 : 2 + 3 + 7 + 13 = 5 + 7 + 13 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by ext))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Algebra.trace_complex_apply | rw [Algebra.trace_complex_apply] | simp only [Algebra.trace_complex_apply]))
    (add unsafe 30% (by first | apply MeasureTheory.OuterMeasure.trim_add | rw [MeasureTheory.OuterMeasure.trim_add] | simp only [MeasureTheory.OuterMeasure.trim_add]))
    (add unsafe 30% (by first | apply Nat.doubleFactorial_add_two | rw [Nat.doubleFactorial_add_two] | simp only [Nat.doubleFactorial_add_two]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_iff_right | rw [Ordinal.nadd_lt_nadd_iff_right] | simp only [Ordinal.nadd_lt_nadd_iff_right]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_le_of_lt | rw [Ordinal.nadd_lt_nadd_of_le_of_lt] | simp only [Ordinal.nadd_lt_nadd_of_le_of_lt]))
    (add unsafe 20% (by first | apply Pell.xy_succ_succ | rw [Pell.xy_succ_succ] | simp only [Pell.xy_succ_succ]))

  have h_sum_primes_add2 : 5 + 7 + 13 = 12 + 13 := by
    clear * -
    aesop (config := {
    useSimpAll              := false
    })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Num.cast_add | rw [Num.cast_add] | simp only [Num.cast_add]))
    (add unsafe 30% (by first | apply Nat.add_comm | rw [Nat.add_comm] | simp only [Nat.add_comm]))
    (add unsafe 30% (by first | apply Num.add_of_nat | rw [Num.add_of_nat] | simp only [Num.add_of_nat]))
    (add unsafe 30% (by first | apply add_idem | rw [add_idem] | simp only [add_idem]))
    (add unsafe 20% (by first | apply Nat.add_succ | rw [Nat.add_succ] | simp only [Nat.add_succ]))

  have h_sum_primes_end : 12 + 13 = 25 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    useSimpAll              := false
    })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Nat.fib_two_mul_add_two | rw [Nat.fib_two_mul_add_two] | simp only [Nat.fib_two_mul_add_two]))
    (add unsafe 10% (by first | apply Nat.fib_two_mul_add_one | rw [Nat.fib_two_mul_add_one] | simp only [Nat.fib_two_mul_add_one]))

  have h_total_sum_primes : ∑ k in {2, 3, 7, 13}, k = 25 := by
    clear * - h_sum_primes_start h_sum_primes_add1 h_sum_primes_add2 h_sum_primes_end
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

  have h_substitute_primes : (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = ∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors 1092), k := by
    clear * - h_a_val
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

  have h_conclusion : (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = 25 := by
    clear * - h_substitute_primes h_primes_1092 h_total_sum_primes
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

  exact h_conclusion
