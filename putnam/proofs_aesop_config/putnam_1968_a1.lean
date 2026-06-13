
import Mathlib

set_option maxHeartbeats 0

theorem putnam_1968_a1
: 22/7 - Real.pi = ∫ x in (0)..1, x^4 * (1 - x)^4 / (1 + x^2) := by
  have h_expand : ∀ x : ℝ, x^4 * (1 - x)^4 = x^8 - 4*x^7 + 6*x^6 - 4*x^5 + x^4 := by
    intro x
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

  have h_poly_identity : ∀ x : ℝ, x^8 - 4*x^7 + 6*x^6 - 4*x^5 + x^4 = (x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4) * (1 + x^2) - 4 := by
    intro x
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
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_integrand_decomp : ∀ x : ℝ, x^4 * (1 - x)^4 / (1 + x^2) = x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4 - 4 / (1 + x^2) := by
    intro x
    clear * - h_expand h_poly_identity
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add unsafe 100% (by nlinarith))
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
    (add unsafe 30% (by first | apply AddChar.not_isPrimitive_mulShift | rw [AddChar.not_isPrimitive_mulShift] | simp only [AddChar.not_isPrimitive_mulShift]))
    (add unsafe 30% (by first | apply CompleteSublattice.sSupClosed | rw [CompleteSublattice.sSupClosed] | simp only [CompleteSublattice.sSupClosed]))
    (add unsafe 10% (by first | apply Quaternion.im_nnratCast | rw [Quaternion.im_nnratCast] | simp only [Quaternion.im_nnratCast]))

  have h_integral_eq : ∫ x in (0)..1, x^4 * (1 - x)^4 / (1 + x^2) = ∫ x in (0)..1, (x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4 - 4 / (1 + x^2)) := by
    clear * - h_integrand_decomp
    aesop (config := {
    maxRuleApplications     := 280
    maxGoals                := 64
    enableUnfold            := false
    })
    (add safe 1 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by nlinarith))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by ext))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Finset.insert_inter_distrib | rw [Finset.insert_inter_distrib] | simp only [Finset.insert_inter_distrib]))
    (add unsafe 30% (by first | apply Finset.insert_union | rw [Finset.insert_union] | simp only [Finset.insert_union]))
    (add unsafe 30% (by first | apply Finset.inter_mem_infs | rw [Finset.inter_mem_infs] | simp only [Finset.inter_mem_infs]))
    (add unsafe 30% (by first | apply Finset.union_insert | rw [Finset.union_insert] | simp only [Finset.union_insert]))
    (add unsafe 30% (by first | apply Finset.union_mem_sups | rw [Finset.union_mem_sups] | simp only [Finset.union_mem_sups]))
    (add unsafe 30% (by first | apply collapse_of_mem | rw [collapse_of_mem] | simp only [collapse_of_mem]))
    (add unsafe 30% (by first | apply le_collapse_of_insert_mem | rw [le_collapse_of_insert_mem] | simp only [le_collapse_of_insert_mem]))
    (add unsafe 30% (by first | apply le_collapse_of_mem | rw [le_collapse_of_mem] | simp only [le_collapse_of_mem]))

  have h_integral_eval : ∫ x in (0)..1, (x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4 - 4 / (1 + x^2)) = (1:ℝ)/7 - (2:ℝ)/3 + 1 - (4:ℝ)/3 + 4 - Real.pi := by
    clear * -
    simp_all only [one_div]
    apply Eq.symm <;> ring
    rw [eq_comm]
    rw [intervalIntegral.integral_add]
    · simp_all only [intervalIntegral.intervalIntegrable_pow, intervalIntegral.intervalIntegrable_inv_one_add_sq,
        IntervalIntegrable.mul_const, intervalIntegral.integral_sub, integral_pow, Nat.reduceAdd, one_pow, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Nat.cast_ofNat, one_div,
        intervalIntegral.integral_mul_const, integral_inv_one_add_sq, Real.arctan_one, Real.arctan_zero,
        isUnit_iff_ne_zero, IsUnit.div_mul_cancel]
      norm_num <;> ring
    · apply Continuous.intervalIntegrable <;> norm_num
      exact (by fun_prop)
    ·
      simp_all only [intervalIntegral.intervalIntegrable_pow, intervalIntegral.intervalIntegrable_inv_one_add_sq,
        IntervalIntegrable.mul_const, IntervalIntegrable.sub]

  have h_arith_group : ((1:ℝ)/7 - (2:ℝ)/3 + 1 - (4:ℝ)/3 + 4 - Real.pi) = ((1:ℝ)/7 + 5 - (6:ℝ)/3 - Real.pi) := by
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
    (add unsafe 30% (by first | apply Ioc_mem_nhdsWithin_Iic | rw [Ioc_mem_nhdsWithin_Iic] | simp only [Ioc_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_arith_final : ((1:ℝ)/7 + 5 - (6:ℝ)/3 - Real.pi) = ((22:ℝ)/7 - Real.pi) := by
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
    (add unsafe 30% (by first | apply Ioc_mem_nhdsWithin_Iic | rw [Ioc_mem_nhdsWithin_Iic] | simp only [Ioc_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_main : ∫ x in (0)..1, x^4 * (1 - x)^4 / (1 + x^2) = (22:ℝ)/7 - Real.pi := by
    clear * - h_integral_eq h_integral_eval h_arith_group h_arith_final
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

  exact Eq.symm h_main
