import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  have h_step1 : (3 : ℕ) ! = 3 * 2 * 1 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
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
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by ring_nf))
    (add unsafe 10% (by first | apply Nat.cast_ofNat | rw [Nat.cast_ofNat] | simp only [Nat.cast_ofNat]))
    (add unsafe 10% (by first | apply Quaternion.coe_natCast | rw [Quaternion.coe_natCast] | simp only [Quaternion.coe_natCast]))
    (add unsafe 10% (by first | apply QuaternionAlgebra.coe_natCast | rw [QuaternionAlgebra.coe_natCast] | simp only [QuaternionAlgebra.coe_natCast]))
    (add unsafe 10% (by first | apply QuaternionGroup.a_mul_a | rw [QuaternionGroup.a_mul_a] | simp only [QuaternionGroup.a_mul_a]))
    (add unsafe 10% (by first | apply ZNum.of_natCast | rw [ZNum.of_natCast] | simp only [ZNum.of_natCast]))

  have h_step2 : 3 * 2 * 1 = 6 := by
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
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply two_mul | rw [two_mul] | simp only [two_mul]))
    (add unsafe 10% (by first | apply mul_assoc | rw [mul_assoc] | simp only [mul_assoc]))
    (add unsafe 10% (by first | apply mul_left_comm | rw [mul_left_comm] | simp only [mul_left_comm]))

  have h_step3 : (3 : ℕ) ^ (3 - 1) = 3 ^ 2 := by
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
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Real.two_mul_arctan_sub_pi | rw [Real.two_mul_arctan_sub_pi] | simp only [Real.two_mul_arctan_sub_pi]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq_eq_one_of_squarefree | rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree] | simp only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
    (add unsafe 10% (by first | apply Complex.cpow_two | rw [Complex.cpow_two] | simp only [Complex.cpow_two]))
    (add unsafe 10% (by first | apply QuaternionGroup.a_one_pow_n | rw [QuaternionGroup.a_one_pow_n] | simp only [QuaternionGroup.a_one_pow_n]))

  have h_step4 : (3 : ℕ) ^ 2 = 9 := by
    clear * -
    aesop
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
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
    (add unsafe 40% (by first | apply QuaternionGroup.xa_sq | rw [QuaternionGroup.xa_sq] | simp only [QuaternionGroup.xa_sq]))
    (add unsafe 40% (by first | apply Real.rpow_two | rw [Real.rpow_two] | simp only [Real.rpow_two]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
    (add unsafe 10% (by first | apply CoxeterSystem.simple_sq | rw [CoxeterSystem.simple_sq] | simp only [CoxeterSystem.simple_sq]))
    (add unsafe 10% (by first | apply mul_pow | rw [mul_pow] | simp only [mul_pow]))
    (add unsafe 10% (by first | apply sq_sub_sq | rw [sq_sub_sq] | simp only [sq_sub_sq]))

  have h_step5 : (3 : ℕ) ! < (3 : ℕ) ^ (3 - 1) := by
    clear * - h_step1 h_step2 h_step3 h_step4
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
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_step_inductive : ∀ (k : ℕ), 3 ≤ k → k ! < k ^ (k - 1) → (k + 1) ! < (k + 1) ^ ((k + 1) - 1) := by
    intro k hk IH
    have h_step6 : 3 ≤ k := hk
    have h_step7 : k ! < k ^ (k - 1) := IH
    have h_step8 : (k + 1) ! = (k + 1) * k ! := by
      clear * -
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
      (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_step9 : (k + 1) * k ! < (k + 1) * k ^ (k - 1) := by
      clear * - h_step7
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

    have h_step10 : k < k + 1 := by
      clear * -
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

    have h_step11 : k - 1 ≥ 2 := by
      clear * - h_step6
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

    have h_step12 : k - 1 > 0 := by
      clear * - h_step11
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

    have h_step13 : k ^ (k - 1) < (k + 1) ^ (k - 1) := by
      clear * - h_step10 h_step12
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

    have h_step14 : (k + 1) * k ^ (k - 1) < (k + 1) * (k + 1) ^ (k - 1) := by
      clear * - h_step13
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

    have h_step15 : (k + 1) * (k + 1) ^ (k - 1) = (k + 1) ^ (1 + k - 1) := by
      clear * -
      simp_all only [add_tsub_cancel_left]
      cases k <;> simp
      ring

    have h_step16 : 1 + k - 1 = k := by
      clear * -
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
      (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_step17 : (k + 1) ^ (1 + k - 1) = (k + 1) ^ k := by
      clear * - h_step16
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

    have h_step18 : (k + 1) * k ^ (k - 1) < (k + 1) ^ k := by
      clear * - h_step14 h_step15 h_step17
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

    have h_step19 : (k + 1) ! < (k + 1) ^ k := by
      clear * - h_step8 h_step9 h_step18
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
      (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_step20 : (k + 1) ^ k = (k + 1) ^ ((k + 1) - 1) := by
      clear * -
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

    have h_ind_final : (k + 1) ! < (k + 1) ^ ((k + 1) - 1) := by
      clear * - h_step19 h_step20
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
      (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    exact h_ind_final

  simp_all only [reduceMul, mul_one, Nat.add_one_sub_one, reducePow, reduceLT, add_tsub_cancel_right, gt_iff_lt]
  revert n
  intros n h_base
  induction h_base <;> simp_all [factorial, pow_succ]
