
import Mathlib
open Set Function Metric

set_option maxHeartbeats 0

abbrev putnam_1998_b1_solution : ℝ := 6

theorem putnam_1998_b1
: sInf {((x + 1/x)^6 - (x^6 + 1/x^6) - 2)/((x + 1/x)^3 + (x^3 + 1/x^3)) | x > (0 : ℝ)} = putnam_1998_b1_solution := by
  have h_u_ge_2 : ∀ (x : ℝ), x > (0:ℝ) → x + (1:ℝ)/x ≥ (2:ℝ) := by
    clear * -
    simp_all only [gt_iff_lt, one_div, ge_iff_le]
    refine' fun x hx => le_of_sub_nonneg _
    simp_all only [sub_nonneg]
    field_simp [hx.ne.symm, hx.ne']
    rw [le_div_iff (hx)] <;> nlinarith [sq_nonneg (x - 1)]

  have h_cube_identity : ∀ (x : ℝ), x ≠ (0:ℝ) → x^3 + (1:ℝ)/x^3 = (x + (1:ℝ)/x)^3 - 3*(x + (1:ℝ)/x) := by
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
    (add unsafe 30% (by first | apply LieModuleHom.coe_linear_mk | rw [LieModuleHom.coe_linear_mk] | simp only [LieModuleHom.coe_linear_mk]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_sixth_power_identity : ∀ (x : ℝ), x ≠ (0:ℝ) → x^6 + (1:ℝ)/x^6 = (x^3 + (1:ℝ)/x^3)^2 - (2:ℝ) := by
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
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_sixth_expanded : ∀ (x : ℝ), x ≠ (0:ℝ) → x^6 + (1:ℝ)/x^6 = ((x + (1:ℝ)/x)^3 - 3*(x + (1:ℝ)/x))^2 - (2:ℝ) := by
    clear * - h_sixth_power_identity h_cube_identity
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

  have h_num_factor : ∀ (u : ℝ), u^6 - (((u^3 - 3*u)^2 - 2) : ℝ) - 2 = 3*u^2*(2*u^2 - 3) := by
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
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_lt_of_le | rw [Ordinal.nadd_lt_nadd_of_lt_of_le] | simp only [Ordinal.nadd_lt_nadd_of_lt_of_le]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.Quotient.eq' | rw [Submodule.Quotient.eq'] | simp only [Submodule.Quotient.eq']))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_denom_factor : ∀ (u : ℝ), u^3 + (u^3 - 3*u) = u*(2*u^2 - 3) := by
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
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_lt_of_le | rw [Ordinal.nadd_lt_nadd_of_lt_of_le] | simp only [Ordinal.nadd_lt_nadd_of_lt_of_le]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_denom_positive : ∀ (u : ℝ), u ≥ (2:ℝ) → 2*u^2 - 3 > (0:ℝ) := by
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
    (add unsafe 30% (by first | apply ENat.le_of_lt_add_one | rw [ENat.le_of_lt_add_one] | simp only [ENat.le_of_lt_add_one]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_le_of_lt | rw [Ordinal.nadd_lt_nadd_of_le_of_lt] | simp only [Ordinal.nadd_lt_nadd_of_le_of_lt]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_lt_of_le | rw [Ordinal.nadd_lt_nadd_of_lt_of_le] | simp only [Ordinal.nadd_lt_nadd_of_lt_of_le]))

  have h_f_simplified : ∀ (x : ℝ), x > (0:ℝ) →
    ((x + (1:ℝ)/x)^6 - (x^6 + (1:ℝ)/x^6) - 2)/((x + (1:ℝ)/x)^3 + (x^3 + (1:ℝ)/x^3)) =
    3*(x + (1:ℝ)/x) := by
    clear * - h_u_ge_2 h_cube_identity h_sixth_expanded h_num_factor h_denom_factor h_denom_positive
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

  have h_lower_bound : ∀ (x : ℝ), x > (0:ℝ) →
    ((x + (1:ℝ)/x)^6 - (x^6 + (1:ℝ)/x^6) - 2)/((x + (1:ℝ)/x)^3 + (x^3 + (1:ℝ)/x^3)) ≥ (6:ℝ) := by
    clear * - h_u_ge_2 h_f_simplified
    simp_all only [gt_iff_lt, one_div, ge_iff_le]
    exact fun x hx => by linarith [h_u_ge_2 x hx]

  have h_inf_eq_6 : sInf {((x + (1:ℝ)/x)^6 - (x^6 + (1:ℝ)/x^6) - 2)/((x + (1:ℝ)/x)^3 + (x^3 + (1:ℝ)/x^3)) | x > (0:ℝ)} = (6:ℝ) := by
    clear * - h_lower_bound
    simp_all only [gt_iff_lt, one_div, ge_iff_le]
    apply le_antisymm
    · have h_ub := h_lower_bound 1 (by norm_num)
      simp_all only [inv_one, one_pow, ge_iff_le]
      refine csInf_le ?_ ?_
      · use 6
        norm_num at h_ub ⊢
        simp_all only
        simp (config := { contextual := true }) [lowerBounds, h_lower_bound]
      · simp_all only [mem_setOf_eq]
        refine ⟨1, by positivity, ?_⟩ <;> norm_num
    · apply le_csInf
      · exact ⟨6, by exact ⟨1, by norm_num, by norm_num⟩⟩
      · simp_all only [mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true]

  have h_final : sInf {((x + 1/x)^6 - (x^6 + 1/x^6) - 2)/((x + 1/x)^3 + (x^3 + 1/x^3)) | x > (0 : ℝ)} = putnam_1998_b1_solution := by
    clear * - h_inf_eq_6
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
    (add unsafe 30% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  exact h_final
