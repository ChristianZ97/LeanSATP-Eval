import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  have h1 : (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = (16 * ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) := by
    have h1_inner : a ^ 2 = (8 : ℝ) ^ 2 := by
      clear * - h₀
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

    clear * - h1_inner
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

  have h2 : (16 * ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = (16 * (64 : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) := by
    have h2_fact : ((8 : ℝ) ^ 2) = (64 : ℝ) := by
      clear * -
      aesop (config := {
      maxGoals                := 64
      enableUnfold            := false
      })
      (add safe 2 (by ring))
      (add safe 3 (by norm_cast))
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by exfalso))
      (add unsafe 100% (by ring_nf))
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
      (add unsafe 40% (by first | apply Nat.cast_two | rw [Nat.cast_two] | simp only [Nat.cast_two]))
      (add unsafe 40% (by first | apply QuaternionGroup.xa_sq | rw [QuaternionGroup.xa_sq] | simp only [QuaternionGroup.xa_sq]))
      (add unsafe 40% (by first | apply Real.rpow_two | rw [Real.rpow_two] | simp only [Real.rpow_two]))
      (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
      (add unsafe 10% (by first | apply Quaternion.coe_pow | rw [Quaternion.coe_pow] | simp only [Quaternion.coe_pow]))
      (add unsafe 10% (by first | apply mul_pow | rw [mul_pow] | simp only [mul_pow]))
      (add unsafe 10% (by first | apply sq_sub_sq | rw [sq_sub_sq] | simp only [sq_sub_sq]))
      (add unsafe 10% (by first | apply two_ne_zero | rw [two_ne_zero] | simp only [two_ne_zero]))

    clear * - h2_fact
    simp_all only [one_div]

  have h3 : (16 * (64 : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = (16 * (4 : ℝ)) ^ ((1 : ℝ) / 3) := by
    have h3_fact : (64 : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
      clear * -
      simp_all only [one_div]
      rw [Real.rpow_def_of_pos (by norm_num)] <;> norm_cast
      field_simp [show (64 : ℝ) = 2 ^ 6 by norm_cast] <;> ring
      simp [exp_mul, exp_log] <;> norm_num

    clear * - h3_fact
    simp_all only [one_div]

  have h4 : (16 * (4 : ℝ)) ^ ((1 : ℝ) / 3) = (64 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h4_fact : (16 : ℝ) * (4 : ℝ) = (64 : ℝ) := by
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
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by bound))
      (add unsafe 90% (by ext))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by linarith))
      (add unsafe 90% (by nlinarith))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 90% (by simp))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by interval_cases))
      (add unsafe 70% (by exfalso))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 40% (by first | apply Quaternion.self_add_star | rw [Quaternion.self_add_star] | simp only [Quaternion.self_add_star]))
      (add unsafe 40% (by first | apply Quaternion.star_add_self | rw [Quaternion.star_add_self] | simp only [Quaternion.star_add_self]))

    clear * - h4_fact
    aesop (config := {
    maxRuleApplications     := 220
    maxGoals                := 64
    useSimpAll              := false
    enableUnfold            := false
    })
    (add safe 1 (by ring))
    (add safe 2 (by field_simp))
    (add safe 2 (by zify))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Quaternion.normSq_coe | rw [Quaternion.normSq_coe] | simp only [Quaternion.normSq_coe]))
    (add unsafe 10% (by first | apply Quaternion.coe_pow | rw [Quaternion.coe_pow] | simp only [Quaternion.coe_pow]))
    (add unsafe 10% (by first | apply Quaternion.normSq_zpow | rw [Quaternion.normSq_zpow] | simp only [Quaternion.normSq_zpow]))
    (add unsafe 10% (by first | apply Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq | rw [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq] | simp only [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq]))

  have h5 : (64 : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
    have h5_fact : (64 : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
      clear * -
      simp_all only [one_div]
      rw [eq_comm]
      have : (64 : ℝ) = (4 : ℝ) ^ 3
      · norm_num
      · simp_all only
        simp [← this, Real.rpow_def_of_pos]
        simp_all only [Real.log_pow, Nat.cast_ofNat]
        field_simp [exp_log, mul_comm] <;> ring

    clear * - h5_fact
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

  have h_final : (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
    clear * - h1 h2 h3 h4 h5
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

  exact h_final
