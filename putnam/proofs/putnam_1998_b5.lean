
import Mathlib
open Set Function Metric

set_option maxHeartbeats 0

abbrev putnam_1998_b5_solution : ℕ := 1

theorem putnam_1998_b5
(N : ℕ)
(hN : N = ∑ i ∈ Finset.range 1998, 10^i)
: putnam_1998_b5_solution = (Nat.floor (10^1000 * Real.sqrt N)) % 10 := by
  have h_sum_formula : 9 * N = 10^1998 - 1 := by
    clear * - hN
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply DoubleCentralizer.zero_toProd | rw [DoubleCentralizer.zero_toProd] | simp only [DoubleCentralizer.zero_toProd]))
    (add unsafe 40% (by first | apply Ico_mem_nhdsWithin_Iic | rw [Ico_mem_nhdsWithin_Iic] | simp only [Ico_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  let M_nat : ℕ := 10^1999
  have h_M_val : M_nat = 10^1999 := rfl

  let M : ℝ := (M_nat : ℝ)

  have h_N_real_rel : (9 : ℝ) * (N : ℝ) = (10 : ℝ)^1998 - 1 := by
    clear * - h_sum_formula
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply DoubleCentralizer.zero_toProd | rw [DoubleCentralizer.zero_toProd] | simp only [DoubleCentralizer.zero_toProd]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_sq_term : (10 : ℝ)^2000 * (N : ℝ) = (M^2 - 10 * M) / 9 := by
    clear * - h_N_real_rel h_M_val
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply Submodule.Quotient.mk_sub | rw [Submodule.Quotient.mk_sub] | simp only [Submodule.Quotient.mk_sub]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_lb_sq : ((M - 7) / 3)^2 = (M^2 - 14 * M + 49) / 9 := by
    clear * -
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply DoubleCentralizer.zero_toProd | rw [DoubleCentralizer.zero_toProd] | simp only [DoubleCentralizer.zero_toProd]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_ub_sq : ((M - 5) / 3)^2 = (M^2 - 10 * M + 25) / 9 := by
    clear * -
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply DoubleCentralizer.zero_toProd | rw [DoubleCentralizer.zero_toProd] | simp only [DoubleCentralizer.zero_toProd]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_ineq_lb : ((M - 7) / 3)^2 < (10 : ℝ)^2000 * (N : ℝ) := by
    clear * - h_sq_term h_lb_sq h_M_val
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply Submodule.Quotient.mk_sub | rw [Submodule.Quotient.mk_sub] | simp only [Submodule.Quotient.mk_sub]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_ineq_ub : (10 : ℝ)^2000 * (N : ℝ) < ((M - 5) / 3)^2 := by
    clear * - h_sq_term h_ub_sq
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply Submodule.Quotient.mk_sub | rw [Submodule.Quotient.mk_sub] | simp only [Submodule.Quotient.mk_sub]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_sqrt_identity : Real.sqrt ((10 : ℝ)^2000 * (N : ℝ)) = (10 : ℝ)^1000 * Real.sqrt (N : ℝ) := by
    clear * -
    simp_all only [Nat.ofNat_nonneg, pow_nonneg, Real.sqrt_mul, mul_eq_mul_right_iff, Nat.cast_nonneg, Real.sqrt_eq_zero,
      Nat.cast_eq_zero]
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]

  have h_bounds : (M - 7) / 3 < (10 : ℝ)^1000 * Real.sqrt (N : ℝ) ∧
                  (10 : ℝ)^1000 * Real.sqrt (N : ℝ) < (M - 5) / 3 := by
    clear * - h_ineq_lb h_ineq_ub h_sqrt_identity h_M_val
    simp_all [M_nat, M]
    classical aesop
    · rw [← not_le]
      simp_all
      nlinarith [Real.sqrt_nonneg N, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)]
    · rw [mul_comm]
      rw [mul_comm]
      rw [Real.sqrt_eq_iff_sq_eq] at h
      · nlinarith [Real.sqrt_nonneg ↑N, Real.sq_sqrt (by norm_cast; nlinarith : (0 : ℝ) ≤ ↑N)]
      · simp_all
      · simp_all
    · classical nlinarith
    · norm_num1 at *

  have h_M_mod_3 : M_nat % 3 = 1 := by
    clear * - h_M_val
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply Ico_mem_nhdsWithin_Iic | rw [Ico_mem_nhdsWithin_Iic] | simp only [Ico_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_M_minus_7_div : (M_nat - 7) % 3 = 0 := by
    clear * - h_M_mod_3
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply DoubleCentralizer.zero_toProd | rw [DoubleCentralizer.zero_toProd] | simp only [DoubleCentralizer.zero_toProd]))
    (add unsafe 40% (by first | apply Ico_mem_nhdsWithin_Iic | rw [Ico_mem_nhdsWithin_Iic] | simp only [Ico_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  let k : ℕ := (M_nat - 7) / 3

  have h_k_real : (k : ℝ) = (M - 7) / 3 := by
    clear * - h_M_minus_7_div h_M_val
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_ub_real : (M - 5) / 3 = (k : ℝ) + 2 / 3 := by
    clear * - h_k_real
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply Submodule.Quotient.mk_sub | rw [Submodule.Quotient.mk_sub] | simp only [Submodule.Quotient.mk_sub]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_k_bounds : (k : ℝ) < (10 : ℝ)^1000 * Real.sqrt (N : ℝ) ∧
                    (10 : ℝ)^1000 * Real.sqrt (N : ℝ) < (k : ℝ) + 2 / 3 := by
    clear * - h_bounds h_k_real h_ub_real
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply DoubleCentralizer.zero_toProd | rw [DoubleCentralizer.zero_toProd] | simp only [DoubleCentralizer.zero_toProd]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_floor : Nat.floor ((10 : ℝ)^1000 * Real.sqrt (N : ℝ)) = k := by
    clear * - h_k_bounds
    simp_all only [k, M_nat]
    rw [Nat.floor_eq_iff] <;> norm_cast
    · simp_all only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      refine ⟨?_, ?_⟩ <;> linarith [h_k_bounds]
    · simp_all

  have h_k_mod_10 : k % 10 = 1 := by
    clear * - h_M_val h_M_minus_7_div
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 40% (by first | apply DoubleCentralizer.zero_toProd | rw [DoubleCentralizer.zero_toProd] | simp only [DoubleCentralizer.zero_toProd]))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_final : putnam_1998_b5_solution = (Nat.floor (10^1000 * Real.sqrt N)) % 10 := by
    clear * - h_floor h_k_mod_10
    aesop (config := {
    maxRuleApplications     := 260
  })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by omega))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_cast at *))
    (add unsafe 90% (by ring_nf at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp_all))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 20% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 20% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
    (add unsafe 20% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 20% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 20% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  exact h_final
