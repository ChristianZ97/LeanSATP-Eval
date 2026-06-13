import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h_univ

  let a : ℤ := 2
  let b : ℤ := 0

  have h_a_val : a = 2 := by
    clear * -
    aesop
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
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Int.cast_two | rw [Int.cast_two] | simp only [Int.cast_two]))
    (add unsafe 10% (by first | apply Nat.cast_two | rw [Nat.cast_two] | simp only [Nat.cast_two]))
    (add unsafe 10% (by first | apply Nat.factorial_two | rw [Nat.factorial_two] | simp only [Nat.factorial_two]))

  have h_b_val : b = 0 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    })
    (add safe 1 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Ordinal.zero_nadd | rw [Ordinal.zero_nadd] | simp only [Ordinal.zero_nadd]))
    (add unsafe 10% (by first | apply Ordinal.div_zero | rw [Ordinal.div_zero] | simp only [Ordinal.div_zero]))
    (add unsafe 10% (by first | apply Ordinal.nmul_zero | rw [Ordinal.nmul_zero] | simp only [Ordinal.nmul_zero]))
    (add unsafe 10% (by first | apply Ordinal.zero_div | rw [Ordinal.zero_div] | simp only [Ordinal.zero_div]))
    (add unsafe 10% (by first | apply Ordinal.zero_sub | rw [Ordinal.zero_sub] | simp only [Ordinal.zero_sub]))
    (add unsafe 10% (by first | apply OreLocalization.zero_oreDiv | rw [OreLocalization.zero_oreDiv] | simp only [OreLocalization.zero_oreDiv]))

  have h_step3 : a = 2 * 1 := by
    clear * - h_a_val
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
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 40% (by first | apply IsLprojection.mul_compl_self | rw [IsLprojection.mul_compl_self] | simp only [IsLprojection.mul_compl_self]))
    (add unsafe 40% (by first | apply LaurentPolynomial.T_zero | rw [LaurentPolynomial.T_zero] | simp only [LaurentPolynomial.T_zero]))

  have h_step4 : b = 2 * 0 := by
    clear * - h_b_val
    aesop (config := {
    maxNormIterations       := 160
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add safe 4 (by ring))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 20% (by first | apply IsLprojection.mul_compl_self | rw [IsLprojection.mul_compl_self] | simp only [IsLprojection.mul_compl_self]))
    (add unsafe 10% (by first | apply MulZeroClass | rw [MulZeroClass] | simp only [MulZeroClass]))
    (add unsafe 10% (by first | apply WeierstrassCurve.ψ_zero | rw [WeierstrassCurve.ψ_zero] | simp only [WeierstrassCurve.ψ_zero]))
    (add unsafe 10% (by first | apply Zsqrtd.zero_re | rw [Zsqrtd.zero_re] | simp only [Zsqrtd.zero_re]))
    (add unsafe 10% (by first | apply zero_div | rw [zero_div] | simp only [zero_div]))
    (add unsafe 10% (by first | apply zero_pow | rw [zero_pow] | simp only [zero_pow]))

  have h_a_even : ∃ i : ℤ, a = 2 * i := by
    clear * - h_step3
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by ext))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply QuadraticForm.IsometryEquiv.toIsometry | rw [QuadraticForm.IsometryEquiv.toIsometry] | simp only [QuadraticForm.IsometryEquiv.toIsometry]))
    (add unsafe 10% (by first | apply Or.resolve_left | rw [Or.resolve_left] | simp only [Or.resolve_left]))

  have h_b_even : ∃ j : ℤ, b = 2 * j := by
    clear * - h_step4
    aesop
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add unsafe 100% (by nlinarith))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 80% (by norm_num [*] at *))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by ext))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 40% (by first | apply Subtype.ext | rw [Subtype.ext] | simp only [Subtype.ext]))
    (add unsafe 40% (by first | apply Sym2.eq_of_ne_mem | rw [Sym2.eq_of_ne_mem] | simp only [Sym2.eq_of_ne_mem]))
    (add unsafe 30% (by first | apply Eq.symm | rw [Eq.symm] | simp only [Eq.symm]))
    (add unsafe 30% (by first | apply Eq.trans | rw [Eq.trans] | simp only [Eq.trans]))
    (add unsafe 20% (by first | apply vsub_left_cancel | rw [vsub_left_cancel] | simp only [vsub_left_cancel]))

  have h_LHS_top : (∃ i j, a = 2 * i ∧ b = 2 * j) := by
    clear * - h_a_even h_b_even
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

  have h_step5 : a ^ 2 = (2 * 1) ^ 2 := by
    clear * - h_step3
    aesop
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add safe 4 (by ring))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 80% (by norm_num [*] at *))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 40% (by first | apply Subtype.ext | rw [Subtype.ext] | simp only [Subtype.ext]))
    (add unsafe 40% (by first | apply vsub_left_cancel | rw [vsub_left_cancel] | simp only [vsub_left_cancel]))
    (add unsafe 20% (by first | apply Eq.symm | rw [Eq.symm] | simp only [Eq.symm]))
    (add unsafe 20% (by first | apply Eq.trans | rw [Eq.trans] | simp only [Eq.trans]))

  have h_step6 : a ^ 2 = 2 ^ 2 * 1 ^ 2 := by
    clear * - h_step5
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply LieIdeal.mem_map_of_surjective | rw [LieIdeal.mem_map_of_surjective] | simp only [LieIdeal.mem_map_of_surjective]))

  have h_step7 : a ^ 2 = 4 * 1 := by
    clear * - h_step6
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add unsafe 100% (by nlinarith))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by ext))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 30% (by first | apply LieSubmodule.Quotient.mk | rw [LieSubmodule.Quotient.mk] | simp only [LieSubmodule.Quotient.mk]))
    (add unsafe 30% (by first | apply Or.resolve_left | rw [Or.resolve_left] | simp only [Or.resolve_left]))
    (add unsafe 30% (by first | apply Or.resolve_right | rw [Or.resolve_right] | simp only [Or.resolve_right]))

  have h_step8 : a ^ 2 = 4 := by
    clear * - h_step7
    aesop (config := {
    maxNormIterations       := 120
    useSimpAll              := false
    })
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add unsafe 100% (by nlinarith))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by bound))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 80% (by norm_num [*] at *))
    (add unsafe 70% (by ext))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 40% (by first | apply Subtype.ext | rw [Subtype.ext] | simp only [Subtype.ext]))
    (add unsafe 30% (by first | apply Or.resolve_right | rw [Or.resolve_right] | simp only [Or.resolve_right]))
    (add unsafe 30% (by first | apply WeierstrassCurve.Affine.Y_eq_of_Y_ne | rw [WeierstrassCurve.Affine.Y_eq_of_Y_ne] | simp only [WeierstrassCurve.Affine.Y_eq_of_Y_ne]))
    (add unsafe 20% (by first | apply Eq.symm | rw [Eq.symm] | simp only [Eq.symm]))
    (add unsafe 10% (by first | apply Or.resolve_left | rw [Or.resolve_left] | simp only [Or.resolve_left]))

  have h_step9 : b ^ 2 = (2 * 0) ^ 2 := by
    clear * - h_step4
    aesop (config := {
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add safe 4 (by ring))
    (add unsafe 100% (by ring_nf))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply sq_eq_zero_iff | rw [sq_eq_zero_iff] | simp only [sq_eq_zero_iff]))
    (add unsafe 10% (by first | apply MulZeroClass | rw [MulZeroClass] | simp only [MulZeroClass]))
    (add unsafe 10% (by first | apply OfNat.ofNat_ne_zero | rw [OfNat.ofNat_ne_zero] | simp only [OfNat.ofNat_ne_zero]))
    (add unsafe 10% (by first | apply legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero | rw [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero] | simp only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
    (add unsafe 10% (by first | apply legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero' | rw [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero'] | simp only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
    (add unsafe 10% (by first | apply pow_eq_zero | rw [pow_eq_zero] | simp only [pow_eq_zero]))
    (add unsafe 10% (by first | apply pow_eq_zero_iff | rw [pow_eq_zero_iff] | simp only [pow_eq_zero_iff]))
    (add unsafe 10% (by first | apply zero_pow | rw [zero_pow] | simp only [zero_pow]))

  have h_step10 : b ^ 2 = 2 ^ 2 * 0 ^ 2 := by
    clear * - h_step9
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 3 (by push_neg))
    (add safe 4 (by field_simp))
    (add unsafe 100% (by nlinarith))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
    (add unsafe 30% (by first | apply LieIdeal.mem_map_of_surjective | rw [LieIdeal.mem_map_of_surjective] | simp only [LieIdeal.mem_map_of_surjective]))
    (add unsafe 30% (by first | apply LieSubmodule.Quotient.mk | rw [LieSubmodule.Quotient.mk] | simp only [LieSubmodule.Quotient.mk]))
    (add unsafe 30% (by first | apply MvPolynomial.IsWeightedHomogeneous.mul | rw [MvPolynomial.IsWeightedHomogeneous.mul] | simp only [MvPolynomial.IsWeightedHomogeneous.mul]))

  have h_step11 : b ^ 2 = 4 * 0 := by
    clear * - h_step10
    aesop (config := {
    maxRuleApplications     := 280
    maxNormIterations       := 120
    enableUnfold            := false
    })
    (add safe 1 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by ext))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Finset.insert_inter_distrib | rw [Finset.insert_inter_distrib] | simp only [Finset.insert_inter_distrib]))
    (add unsafe 30% (by first | apply Finset.insert_inter_of_not_mem | rw [Finset.insert_inter_of_not_mem] | simp only [Finset.insert_inter_of_not_mem]))
    (add unsafe 30% (by first | apply Finset.inter_mem_infs | rw [Finset.inter_mem_infs] | simp only [Finset.inter_mem_infs]))
    (add unsafe 30% (by first | apply Finset.union_insert | rw [Finset.union_insert] | simp only [Finset.union_insert]))
    (add unsafe 30% (by first | apply Finset.union_mem_sups | rw [Finset.union_mem_sups] | simp only [Finset.union_mem_sups]))
    (add unsafe 30% (by first | apply collapse_of_mem | rw [collapse_of_mem] | simp only [collapse_of_mem]))
    (add unsafe 30% (by first | apply le_collapse_of_insert_mem | rw [le_collapse_of_insert_mem] | simp only [le_collapse_of_insert_mem]))
    (add unsafe 30% (by first | apply le_collapse_of_mem | rw [le_collapse_of_mem] | simp only [le_collapse_of_mem]))

  have h_step12 : b ^ 2 = 0 := by
    clear * - h_step11
    aesop (config := {
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add safe 4 (by ring))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero' | rw [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero'] | simp only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
    (add unsafe 30% (by first | apply sq_eq_zero_iff | rw [sq_eq_zero_iff] | simp only [sq_eq_zero_iff]))
    (add unsafe 10% (by first | apply OfNat.ofNat_ne_zero | rw [OfNat.ofNat_ne_zero] | simp only [OfNat.ofNat_ne_zero]))
    (add unsafe 10% (by first | apply mul_eq_zero | rw [mul_eq_zero] | simp only [mul_eq_zero]))
    (add unsafe 10% (by first | apply or_self_iff | rw [or_self_iff] | simp only [or_self_iff]))
    (add unsafe 10% (by first | apply pow_eq_zero | rw [pow_eq_zero] | simp only [pow_eq_zero]))
    (add unsafe 10% (by first | apply pow_eq_zero_iff | rw [pow_eq_zero_iff] | simp only [pow_eq_zero_iff]))

  have h_step13 : a ^ 2 + b ^ 2 = 4 + 0 := by
    clear * - h_step8 h_step12
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
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_step14 : a ^ 2 + b ^ 2 = 4 := by
    clear * - h_step13
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 3 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 40% (by first | apply Pell.eq_of_xn_modEq_lem2 | rw [Pell.eq_of_xn_modEq_lem2] | simp only [Pell.eq_of_xn_modEq_lem2]))
    (add unsafe 30% (by first | apply Or.resolve_left | rw [Or.resolve_left] | simp only [Or.resolve_left]))
    (add unsafe 30% (by first | apply Or.resolve_right | rw [Or.resolve_right] | simp only [Or.resolve_right]))
    (add unsafe 20% (by first | apply Eq.symm | rw [Eq.symm] | simp only [Eq.symm]))
    (add unsafe 20% (by first | apply Eq.trans | rw [Eq.trans] | simp only [Eq.trans]))
    (add unsafe 10% (by first | apply Iff | rw [Iff] | simp only [Iff]))

  have h_rhs_form : (∃ k : ℤ, a ^ 2 + b ^ 2 = 8 * k) ↔ (∃ k : ℤ, 4 = 8 * k) := by
    clear * - h_step14
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

  have h_k_qcast : ∀ (k : ℤ), 4 = 8 * k → (k : ℚ) = (4 : ℚ) / 8 := by
    clear * -
    intro z hz
    field_simp [hz.symm]
    norm_cast <;> linarith

  have h_div_simple : (4 : ℚ) / 8 = (1 : ℚ) / 2 := by
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
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by exfalso))
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply div_sub' | rw [div_sub'] | simp only [div_sub']))
    (add unsafe 30% (by first | apply one_div | rw [one_div] | simp only [one_div]))
    (add unsafe 10% (by first | apply Real.sqrt_div_self' | rw [Real.sqrt_div_self'] | simp only [Real.sqrt_div_self']))
    (add unsafe 10% (by first | apply div_self | rw [div_self] | simp only [div_self]))
    (add unsafe 10% (by first | apply inv_eq_one_div | rw [inv_eq_one_div] | simp only [inv_eq_one_div]))
    (add unsafe 10% (by first | apply mul_one_div | rw [mul_one_div] | simp only [mul_one_div]))
    (add unsafe 10% (by first | apply one_sub_div | rw [one_sub_div] | simp only [one_sub_div]))

  have h_k_is_half : ∀ (k : ℤ), 4 = 8 * k → (k : ℚ) = (1 : ℚ) / 2 := by
    clear * - h_k_qcast h_div_simple
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

  have h_half_irrat : ∀ (k : ℤ), (k : ℚ) ≠ (1 : ℚ) / 2 := by
    clear * -
    simp_all only [one_div, ne_eq]
    intro z hz
    cases z
    · simp_all only [Int.ofNat_eq_coe, Int.cast_natCast]
      field_simp at hz <;> norm_cast at hz <;> omega
    · simp_all only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
      norm_num at hz <;> linarith

  have h_step20_bot : ¬ (∃ k : ℤ, 4 = 8 * k) := by
    clear * - h_k_is_half h_half_irrat
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

  have h_RHS_bot : ¬ (∃ k : ℤ, a ^ 2 + b ^ 2 = 8 * k) := by
    clear * - h_rhs_form h_step20_bot
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

  have h_inst : (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
    clear * - h_univ h_a_val h_b_val
    simp_all [a, b]
    specialize h_univ a b <;> aesop

  have h_derive_RHS : ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
    clear * - h_inst h_LHS_top
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

  have h_contra : False := by
    clear * - h_derive_RHS h_RHS_bot
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

  exact h_contra
