import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_321 (n : ZMod 1399) (h₁ : n = 160⁻¹) : n = 1058 := by
  have h_step1 : (119 : ZMod 1399) = -((8 : ZMod 1399) * (160 : ZMod 1399)) := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    })
    (add safe 1 (by norm_num))
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
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
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 30% (by first | apply ArithmeticFunction.coe_zeta_mul_coe_moebius | rw [ArithmeticFunction.coe_zeta_mul_coe_moebius] | simp only [ArithmeticFunction.coe_zeta_mul_coe_moebius]))
    (add unsafe 30% (by first | apply ArithmeticFunction.moebius_mul_coe_zeta | rw [ArithmeticFunction.moebius_mul_coe_zeta] | simp only [ArithmeticFunction.moebius_mul_coe_zeta]))
    (add unsafe 10% (by first | apply ArithmeticFunction.intCoe_one | rw [ArithmeticFunction.intCoe_one] | simp only [ArithmeticFunction.intCoe_one]))

  have h_step2 : (41 : ZMod 1399) = (160 : ZMod 1399) - (119 : ZMod 1399) := by
    clear * -
    aesop (config := {
    maxGoals                := 64
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
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 30% (by first | apply ArithmeticFunction.intCoe_one | rw [ArithmeticFunction.intCoe_one] | simp only [ArithmeticFunction.intCoe_one]))
    (add unsafe 30% (by first | apply ArithmeticFunction.one | rw [ArithmeticFunction.one] | simp only [ArithmeticFunction.one]))
    (add unsafe 10% (by first | apply ArithmeticFunction.coe_coe | rw [ArithmeticFunction.coe_coe] | simp only [ArithmeticFunction.coe_coe]))

  have h_step3 : (37 : ZMod 1399) = (119 : ZMod 1399) - ((2 : ZMod 1399) * (41 : ZMod 1399)) := by
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
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Quaternion.star_add_self' | rw [Quaternion.star_add_self'] | simp only [Quaternion.star_add_self']))
    (add unsafe 20% (by first | apply Quaternion.self_add_star | rw [Quaternion.self_add_star] | simp only [Quaternion.self_add_star]))
    (add unsafe 20% (by first | apply Quaternion.star_add_self | rw [Quaternion.star_add_self] | simp only [Quaternion.star_add_self]))
    (add unsafe 10% (by first | apply mul_two | rw [mul_two] | simp only [mul_two]))

  have h_step4 : (4 : ZMod 1399) = (41 : ZMod 1399) - (37 : ZMod 1399) := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    useSimpAll              := false
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add safe 4 (by ring))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_num [*] at *))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Quaternion.self_add_star | rw [Quaternion.self_add_star] | simp only [Quaternion.self_add_star]))
    (add unsafe 40% (by first | apply Quaternion.star_add_self' | rw [Quaternion.star_add_self'] | simp only [Quaternion.star_add_self']))
    (add unsafe 30% (by first | apply Complex.sin_two_mul | rw [Complex.sin_two_mul] | simp only [Complex.sin_two_mul]))
    (add unsafe 30% (by first | apply Real.sin_two_mul | rw [Real.sin_two_mul] | simp only [Real.sin_two_mul]))

  have h_step5 : (1 : ZMod 1399) = (37 : ZMod 1399) - ((9 : ZMod 1399) * (4 : ZMod 1399)) := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    useSimpAll              := false
    })
    (add safe 1 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by exfalso))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 10% (by first | apply ArithmeticFunction.intCoe_one | rw [ArithmeticFunction.intCoe_one] | simp only [ArithmeticFunction.intCoe_one]))
    (add unsafe 10% (by first | apply ModularGroup.T_pow_mul_apply_one | rw [ModularGroup.T_pow_mul_apply_one] | simp only [ModularGroup.T_pow_mul_apply_one]))
    (add unsafe 10% (by first | apply ModularGroup.g_eq_of_c_eq_one | rw [ModularGroup.g_eq_of_c_eq_one] | simp only [ModularGroup.g_eq_of_c_eq_one]))

  have h_inter1 : (1 : ZMod 1399) = ((10 : ZMod 1399) * (37 : ZMod 1399)) - ((9 : ZMod 1399) * (41 : ZMod 1399)) := by
    clear * - h_step4 h_step5
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
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

  have h_inter2 : (1 : ZMod 1399) = ((10 : ZMod 1399) * (119 : ZMod 1399)) - ((29 : ZMod 1399) * (41 : ZMod 1399)) := by
    clear * - h_step3 h_inter1
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
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

  have h_inter3 : (1 : ZMod 1399) = ((39 : ZMod 1399) * (119 : ZMod 1399)) - ((29 : ZMod 1399) * (160 : ZMod 1399)) := by
    clear * - h_step2 h_inter2
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
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

  have h_euclid_res : (1 : ZMod 1399) = -((341 : ZMod 1399) * (160 : ZMod 1399)) := by
    clear * - h_step1 h_inter3
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
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

  have h_coef_adjust : -((341 : ZMod 1399)) = (1058 : ZMod 1399) := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    enableUnfold            := false
    })
    (add safe 1 (by norm_num))
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 30% (by first | apply Int.negOnePow_neg | rw [Int.negOnePow_neg] | simp only [Int.negOnePow_neg]))
    (add unsafe 30% (by first | apply Int.negOnePow_one | rw [Int.negOnePow_one] | simp only [Int.negOnePow_one]))
    (add unsafe 30% (by first | apply Int.negOnePow_succ | rw [Int.negOnePow_succ] | simp only [Int.negOnePow_succ]))
    (add unsafe 30% (by first | apply Matrix.GLPos.coe_neg_GL | rw [Matrix.GLPos.coe_neg_GL] | simp only [Matrix.GLPos.coe_neg_GL]))
    (add unsafe 30% (by first | apply Units.neg_smul | rw [Units.neg_smul] | simp only [Units.neg_smul]))
    (add unsafe 20% (by first | apply Int.negOnePow_zero | rw [Int.negOnePow_zero] | simp only [Int.negOnePow_zero]))

  have h_inverse_proof : (160 : ZMod 1399) * (1058 : ZMod 1399) = (1 : ZMod 1399) := by
    clear * - h_euclid_res h_coef_adjust
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

  have h_final : n = (1058 : ZMod 1399) := by
    clear * - h₁ h_inverse_proof
    simp_all only
    have h₂ : (160 : ZMod 1399) ≠ 0
    · simp_all only [ne_eq]
      decide
    · simp_all only [ne_eq]
      apply ZMod.inv_eq_of_mul_eq_one
      simp_all only

  exact h_final
