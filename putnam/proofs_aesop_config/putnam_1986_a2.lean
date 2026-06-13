
import Mathlib

set_option maxHeartbeats 0

abbrev putnam_1986_a2_solution : ℕ := 3
theorem putnam_1986_a2
: (Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10 = putnam_1986_a2_solution) := by
  let Y : ℕ := 10 ^ 100
  let y : ℝ := (Y : ℝ)
  let S_sum := ∑ k in Finset.range 200, ((-3 : ℝ) ^ k) * (y ^ (199 - k))
  have h_step2_algebra : y ^ 200 = (y + 3) * S_sum + 3 ^ 200 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    enableUnfold            := false
    })
    (add safe 1 (by norm_num))
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by exfalso))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by ring_nf))
    (add unsafe 10% (by first | apply Nat.cast_npow | rw [Nat.cast_npow] | simp only [Nat.cast_npow]))
    (add unsafe 10% (by first | apply Nat.cast_pow | rw [Nat.cast_pow] | simp only [Nat.cast_pow]))
    (add unsafe 10% (by first | apply PadicInt.coe_pow | rw [PadicInt.coe_pow] | simp only [PadicInt.coe_pow]))
    (add unsafe 10% (by first | apply Quaternion.coe_natCast | rw [Quaternion.coe_natCast] | simp only [Quaternion.coe_natCast]))
    (add unsafe 10% (by first | apply Quaternion.coe_pow | rw [Quaternion.coe_pow] | simp only [Quaternion.coe_pow]))
    (add unsafe 10% (by first | apply Rat.cast_pow | rw [Rat.cast_pow] | simp only [Rat.cast_pow]))

  have h_step3_div : y ^ 200 / (y + 3) = S_sum + 3 ^ 200 / (y + 3) := by
    clear * - h_step2_algebra
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
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_step4_power : (3 : ℝ) ^ 200 = 9 ^ 100 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    enableUnfold            := false
    })
    (add safe 2 (by field_simp))
    (add safe 2 (by ring))
    (add safe 3 (by norm_cast))
    (add safe 4 (by abel))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by exfalso))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 80% (by split))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 40% (by first | apply neg_one_sq | rw [neg_one_sq] | simp only [neg_one_sq]))
    (add unsafe 30% (by first | apply one_pow | rw [one_pow] | simp only [one_pow]))
    (add unsafe 30% (by first | apply pow_mul | rw [pow_mul] | simp only [pow_mul]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq_eq_one_of_squarefree | rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree] | simp only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))

  have h_step5_ineq : (9 : ℝ) ^ 100 < 10 ^ 100 + 3 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_num [*] at *))
    (add unsafe 70% (by ext))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Real.sqrt_lt | rw [Real.sqrt_lt] | simp only [Real.sqrt_lt]))
    (add unsafe 30% (by first | apply Real.sqrt_lt' | rw [Real.sqrt_lt'] | simp only [Real.sqrt_lt']))
    (add unsafe 30% (by first | apply lt_mul_iff_one_lt_left | rw [lt_mul_iff_one_lt_left] | simp only [lt_mul_iff_one_lt_left]))
    (add unsafe 30% (by first | apply pow_lt_one | rw [pow_lt_one] | simp only [pow_lt_one]))
    (add unsafe 30% (by first | apply pow_lt_pow_left | rw [pow_lt_pow_left] | simp only [pow_lt_pow_left]))
    (add unsafe 20% (by first | apply lt_mul_of_le_of_one_lt | rw [lt_mul_of_le_of_one_lt] | simp only [lt_mul_of_le_of_one_lt]))

  have h_step6_bounds : 0 < (3 : ℝ) ^ 200 / (y + 3) ∧ (3 : ℝ) ^ 200 / (y + 3) < 1 := by
    clear * - h_step4_power h_step5_ineq
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

  let S_int : ℤ := ∑ k in Finset.range 200, ((-3 : ℤ) ^ k) * (Y ^ (199 - k) : ℤ)
  have h_sum_is_int : (S_int : ℝ) = S_sum := by
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
    (add unsafe 30% (by first | apply LieModuleHom.coe_linear_mk | rw [LieModuleHom.coe_linear_mk] | simp only [LieModuleHom.coe_linear_mk]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_lt_of_le | rw [Ordinal.nadd_lt_nadd_of_lt_of_le] | simp only [Ordinal.nadd_lt_nadd_of_lt_of_le]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_S_int_nn : 0 ≤ S_int := by
    clear * - h_step2_algebra h_sum_is_int
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

  have h_step7_floor : Nat.floor (y ^ 200 / (y + 3)) = S_int.natAbs := by
    clear * - h_step3_div h_step6_bounds h_sum_is_int h_S_int_nn
    simp_all only [Nat.reducePow, Nat.cast_ofNat, Nat.ofNat_pos, pow_pos, div_pos_iff_of_pos_left, Int.reduceNeg,
      Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_ofNat, y, Y, S_sum, S_int]
    norm_num [Nat.floor_eq_iff]

  have h_expr_match : (10 ^ 20000 : ℝ) / (10 ^ 100 + 3) = y ^ 200 / (y + 3) := by
    clear * -
    aesop (config := {
    maxNormIterations       := 160
    maxGoals                := 64
    })
    (add safe 1 (by norm_num))
    (add safe 2 (by field_simp))
    (add safe 2 (by ring))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by exfalso))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 10% (by first | apply MulZeroClass | rw [MulZeroClass] | simp only [MulZeroClass]))
    (add unsafe 10% (by first | apply Nat.cast_zero | rw [Nat.cast_zero] | simp only [Nat.cast_zero]))
    (add unsafe 10% (by first | apply Quaternion.coe_pow | rw [Quaternion.coe_pow] | simp only [Quaternion.coe_pow]))
    (add unsafe 10% (by first | apply Rat.cast_pow | rw [Rat.cast_pow] | simp only [Rat.cast_pow]))
    (add unsafe 10% (by first | apply Stirling.stirlingSeq | rw [Stirling.stirlingSeq] | simp only [Stirling.stirlingSeq]))

  have h_Y_mod_10 : (Y : ZMod 10) = 0 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    enableUnfold            := false
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
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 10% (by first | apply ArithmeticFunction.const_one_eq_zeta | rw [ArithmeticFunction.const_one_eq_zeta] | simp only [ArithmeticFunction.const_one_eq_zeta]))
    (add unsafe 10% (by first | apply ArithmeticFunction.intCoe_apply | rw [ArithmeticFunction.intCoe_apply] | simp only [ArithmeticFunction.intCoe_apply]))
    (add unsafe 10% (by first | apply ArithmeticFunction.natCoe_apply | rw [ArithmeticFunction.natCoe_apply] | simp only [ArithmeticFunction.natCoe_apply]))
    (add unsafe 10% (by first | apply ArithmeticFunction.natCoe_one | rw [ArithmeticFunction.natCoe_one] | simp only [ArithmeticFunction.natCoe_one]))
    (add unsafe 10% (by first | apply ArithmeticFunction.zeta_apply | rw [ArithmeticFunction.zeta_apply] | simp only [ArithmeticFunction.zeta_apply]))
    (add unsafe 10% (by first | apply LSeries.convolution | rw [LSeries.convolution] | simp only [LSeries.convolution]))
    (add unsafe 10% (by first | apply LSeries.delta | rw [LSeries.delta] | simp only [LSeries.delta]))

  have h_S_mod_10 : (S_int : ZMod 10) = 3 := by
    clear * - h_Y_mod_10
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply List.exists_of_kerase | rw [List.exists_of_kerase] | simp only [List.exists_of_kerase]))
    (add unsafe 30% (by first | apply List.mem_keys_of_mem_keys_kerase | rw [List.mem_keys_of_mem_keys_kerase] | simp only [List.mem_keys_of_mem_keys_kerase]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Set.subset_insert_iff_of_not_mem | rw [Set.subset_insert_iff_of_not_mem] | simp only [Set.subset_insert_iff_of_not_mem]))

  have h_step_final_mod : S_int.natAbs % 10 = 3 := by
    clear * - h_S_mod_10 h_S_int_nn
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

  have h_result : Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10 = 3 := by
    calc
      Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10
      = Nat.floor (y ^ 200 / (y + 3)) % 10 := by
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

      _ = S_int.natAbs % 10 := by
        rw [h_step7_floor]

      _ = 3 := by
        exact h_step_final_mod

  rw [h_result]
