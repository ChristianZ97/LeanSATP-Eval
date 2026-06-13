import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_150 (n : ℕ) (h₀ : ¬Nat.Prime (7 + 30 * n)) : 6 ≤ n := by
  have h_step1 : n < 6 ↔ n ≤ 5 := by
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

  have h_step2 : (7 + 30 * 0 : ℕ) = 7 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 160
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
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 40% (by first | apply IsLprojection.mul_compl_self | rw [IsLprojection.mul_compl_self] | simp only [IsLprojection.mul_compl_self]))
    (add unsafe 40% (by first | apply gronwallBound_ε0 | rw [gronwallBound_ε0] | simp only [gronwallBound_ε0]))
    (add unsafe 10% (by first | apply MulZeroClass | rw [MulZeroClass] | simp only [MulZeroClass]))
    (add unsafe 10% (by first | apply Nat.cast_zero | rw [Nat.cast_zero] | simp only [Nat.cast_zero]))
    (add unsafe 10% (by first | apply WeierstrassCurve.ψ_zero | rw [WeierstrassCurve.ψ_zero] | simp only [WeierstrassCurve.ψ_zero]))

  have h_step3 : Nat.Prime 7 := by
    clear * -
    decide

  have h_step3b : Nat.Prime (7 + 30 * 0) := by
    clear * - h_step2 h_step3
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))

  have h_step4 : (7 + 30 * 1 : ℕ) = 37 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 160
    maxGoals                := 64
    })
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
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 40% (by first | apply IsLprojection.mul_compl_self | rw [IsLprojection.mul_compl_self] | simp only [IsLprojection.mul_compl_self]))
    (add unsafe 40% (by first | apply LaurentPolynomial.T_zero | rw [LaurentPolynomial.T_zero] | simp only [LaurentPolynomial.T_zero]))
    (add unsafe 40% (by first | apply gronwallBound_ε0 | rw [gronwallBound_ε0] | simp only [gronwallBound_ε0]))

  have h_step5 : Nat.Prime 37 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    })
    (add safe 1 (by norm_num))
    (add safe 2 (by ring))
    (add safe 3 (by norm_cast))
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by exfalso))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 80% (by split))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by nlinarith))
    (add unsafe 30% (by first | apply Cubic.degree_of_a_ne_zero | rw [Cubic.degree_of_a_ne_zero] | simp only [Cubic.degree_of_a_ne_zero]))
    (add unsafe 30% (by first | apply Cubic.degree_of_b_ne_zero | rw [Cubic.degree_of_b_ne_zero] | simp only [Cubic.degree_of_b_ne_zero]))
    (add unsafe 30% (by first | apply Cubic.degree_of_d_eq_zero' | rw [Cubic.degree_of_d_eq_zero'] | simp only [Cubic.degree_of_d_eq_zero']))
    (add unsafe 30% (by first | apply Polynomial.degree_eq_iff_natDegree_eq_of_pos | rw [Polynomial.degree_eq_iff_natDegree_eq_of_pos] | simp only [Polynomial.degree_eq_iff_natDegree_eq_of_pos]))
    (add unsafe 10% (by first | apply Nat.fermatPsp_base_one | rw [Nat.fermatPsp_base_one] | simp only [Nat.fermatPsp_base_one]))
    (add unsafe 10% (by first | apply Nat.psp_from_prime_psp | rw [Nat.psp_from_prime_psp] | simp only [Nat.psp_from_prime_psp]))

  have h_step5b : Nat.Prime (7 + 30 * 1) := by
    clear * - h_step4 h_step5
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
    (add unsafe 10% (by first | apply Quaternion.im_nnratCast | rw [Quaternion.im_nnratCast] | simp only [Quaternion.im_nnratCast]))

  have h_step6 : (7 + 30 * 2 : ℕ) = 67 := by
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
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Quaternion.self_add_star | rw [Quaternion.self_add_star] | simp only [Quaternion.self_add_star]))
    (add unsafe 40% (by first | apply mul_two | rw [mul_two] | simp only [mul_two]))
    (add unsafe 40% (by first | apply two_mul | rw [two_mul] | simp only [two_mul]))

  have h_step7 : Nat.Prime 67 := by
    clear * -
    norm_num

  have h_step7b : Nat.Prime (7 + 30 * 2) := by
    clear * - h_step6 h_step7
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
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_step8 : (7 + 30 * 3 : ℕ) = 97 := by
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
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))

  have h_step9 : Nat.Prime 97 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    enableUnfold            := false
    })
    (add safe 1 (by norm_num))
    (add safe 2 (by ring))
    (add safe 3 (by norm_cast))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 80% (by split))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by nlinarith))
    (add unsafe 30% (by first | apply Int.natAbs_ofNat | rw [Int.natAbs_ofNat] | simp only [Int.natAbs_ofNat]))
    (add unsafe 30% (by first | apply Int.natAbs_one | rw [Int.natAbs_one] | simp only [Int.natAbs_one]))
    (add unsafe 30% (by first | apply padicNorm.int_eq_one_iff | rw [padicNorm.int_eq_one_iff] | simp only [padicNorm.int_eq_one_iff]))
    (add unsafe 10% (by first | apply Int.cast_natAbs | rw [Int.cast_natAbs] | simp only [Int.cast_natAbs]))
    (add unsafe 10% (by first | apply Int.natAbs | rw [Int.natAbs] | simp only [Int.natAbs]))
    (add unsafe 10% (by first | apply Int.natAbs_cast | rw [Int.natAbs_cast] | simp only [Int.natAbs_cast]))
    (add unsafe 10% (by first | apply Int.natAbs_dvd | rw [Int.natAbs_dvd] | simp only [Int.natAbs_dvd]))
    (add unsafe 10% (by first | apply Int.natCast_natAbs | rw [Int.natCast_natAbs] | simp only [Int.natCast_natAbs]))

  have h_step9b : Nat.Prime (7 + 30 * 3) := by
    clear * - h_step8 h_step9
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
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_step10 : (7 + 30 * 4 : ℕ) = 127 := by
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
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply ArithmeticFunction.moebius_mul_coe_zeta | rw [ArithmeticFunction.moebius_mul_coe_zeta] | simp only [ArithmeticFunction.moebius_mul_coe_zeta]))
    (add unsafe 10% (by first | apply QuaternionAlgebra.coe_commutes | rw [QuaternionAlgebra.coe_commutes] | simp only [QuaternionAlgebra.coe_commutes]))

  have h_step11 : Nat.Prime 127 := by
    clear * -
    norm_num1

  have h_step11b : Nat.Prime (7 + 30 * 4) := by
    clear * - h_step10 h_step11
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
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 10% (by first | apply Quaternion.im_nnratCast | rw [Quaternion.im_nnratCast] | simp only [Quaternion.im_nnratCast]))

  have h_step12 : (7 + 30 * 5 : ℕ) = 157 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 160
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
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 20% (by first | apply DualNumber.snd_eps | rw [DualNumber.snd_eps] | simp only [DualNumber.snd_eps]))

  have h_step13 : Nat.Prime 157 := by
    clear * -
    norm_num

  have h_step13b : Nat.Prime (7 + 30 * 5) := by
    clear * - h_step12 h_step13
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
    (add unsafe 10% (by first | apply Quaternion.im_nnratCast | rw [Quaternion.im_nnratCast] | simp only [Quaternion.im_nnratCast]))

  have h_step14 : ∀ k, k < 6 → Nat.Prime (7 + 30 * k) := by
    clear * - h_step3b h_step5b h_step7b h_step9b h_step11b h_step13b
    simp_all only [mul_zero, add_zero, mul_one, reduceAdd, reduceMul]
    intros k hk
    interval_cases k <;> norm_num at hk ⊢ <;> aesop

  have h_step15 : n < 6 → Nat.Prime (7 + 30 * n) := by
    clear * - h_step14
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

  have h_step16 : ¬(n < 6) := by
    clear * - h_step15 h₀
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

  have h_step17 : 6 ≤ n := by
    clear * - h_step16
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

  exact h_step17
