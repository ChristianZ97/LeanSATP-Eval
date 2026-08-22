
import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_2_3_2 {G : Type*} [Group G] (a b : G) :
  ∃ g : G, b* a = g * a * b * g⁻¹ := by
  -- Step 1: We need to find a g such that b * a = g * a * b * g⁻¹
  -- Let's try g = b as suggested in the informal proof
  let g : G := b
  have h1 : b * a = b * a * b * b⁻¹ := by
    -- This is essentially saying b * a = b * a * e after simplification
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 16
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_inv_rev]))
      (add norm 0 (by grind only [mul_inv_cancel_left]))
      (add norm 0 (by grind only [mul_inv_eq_iff_eq_mul]))
      (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add norm 0 (by grind only [conj_mul]))
      (add norm 0 (by grind only [Equiv.Perm.sameCycle_conj]))
      (add norm 0 (by grind only [inv_mul_cancel_left]))
      (add norm 0 (by grind only [commutatorElement_def]))
      (add norm 0 (by grind only [Subgroup.MemLeftTransversals.inv_mul_toFun_mem]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [eq_inv_mul_iff_mul_eq]))
      (add norm 0 (by grind only [eq_mul_inv_iff_mul_eq]))
      (add norm 0 (by grind only [CategoryTheory.PresheafOfGroups.Cochain₀.inv_apply]))
      (add norm 0 (by grind only [Equiv.Perm.cycleType_conj]))
      (add norm 0 (by grind only [mul_inv_cancel_right]))
      (add norm 0 (by grind only [HNNExtension.equiv_symm_eq_conj]))
      (add norm 0 (by grind only [inv_mul_eq_iff_eq_mul]))
      (add norm 0 (by grind only [Subgroup.coe_inv]))
      (add norm 0 (by grind only [Equiv.Perm.SameCycle.conj]))
      (add norm 0 (by grind only [MulAut.conj]))
      (add norm 0 (by grind only [groupCohomology.twoCocycles_map_one_fst]))
      (add norm 0 (by grind only [MulAut.conj_symm_apply]))
      (add norm 0 (by grind only [Equiv.Perm.Disjoint.cycleType]))
      (add norm 0 (by grind only [Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub]))
      (add norm 0 (by grind only [Equiv.Perm.card_support_conj]))
      (add norm 0 (by grind only [inv_mul_self]))
      (add unsafe 50% (by nlinarith [mul_inv_self]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))
      (add unsafe 50% (by nlinarith [MulAut.conj_inv_apply]))
      (add unsafe 50% (by nlinarith [MulAut.conj_apply]))
      (add unsafe 50% (by nlinarith [mul_right_inv]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))

  have h2 : b * a * b * b⁻¹ = b * a * (b * b⁻¹) := by
    -- Associativity of group operation
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 16
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [conj_mul]))
      (add norm 0 (by grind only [mul_inv_rev]))
      (add norm 0 (by grind only [HNNExtension.equiv_symm_eq_conj]))
      (add norm 0 (by grind only [mul_inv_cancel_left]))
      (add norm 0 (by grind only [Equiv.Perm.sameCycle_conj]))
      (add norm 0 (by grind only [mul_inv_eq_iff_eq_mul]))
      (add norm 0 (by grind only [Equiv.Perm.cycleType_conj]))
      (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [eq_inv_mul_iff_mul_eq]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [inv_mul_cancel_left]))
      (add norm 0 (by grind only [commutatorElement_def]))
      (add norm 0 (by grind only [eq_mul_inv_iff_mul_eq]))
      (add norm 0 (by grind only [Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub]))
      (add norm 0 (by grind only [Equiv.Perm.card_support_conj]))
      (add norm 0 (by grind only [Equiv.Perm.Disjoint.cycleType]))
      (add norm 0 (by grind only [Equiv.Perm.SameCycle.conj]))
      (add norm 0 (by grind only [Subgroup.MemLeftTransversals.inv_mul_toFun_mem]))
      (add norm 0 (by grind only [mul_inv_cancel_right]))
      (add norm 0 (by grind only [Subgroup.coe_mul]))
      (add norm 0 (by grind only [inv_mul_eq_iff_eq_mul]))
      (add norm 0 (by grind only [HNNExtension.equiv_eq_conj]))
      (add norm 0 (by grind only [Subgroup.IsComplement.equiv_fst_eq_mul_inv]))
      (add norm 0 (by grind only [CategoryTheory.PresheafOfGroups.Cochain₀.inv_apply]))
      (add norm 0 (by grind only [Subgroup.IsComplement.equiv_snd_eq_inv_mul]))
      (add norm 0 (by grind only [Subgroup.coe_inv]))
      (add norm 0 (by grind only [MulAut.conj]))
      (add unsafe 50% (by nlinarith [mul_inv_self]))
      (add unsafe 50% (by nlinarith [MulAut.conj_inv_apply]))

  have h3 : b * b⁻¹ = 1 := by
    -- Inverse property
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [CategoryTheory.PresheafOfGroups.Cochain₀.inv_apply]))
      (add norm 0 (by grind only [Subgroup.MemLeftTransversals.inv_mul_toFun_mem]))
      (add norm 0 (by grind only [IsKleinFour.inv_eq_self]))
      (add norm 0 (by grind only [Subgroup.coe_inv]))
      (add norm 0 (by grind only [mul_inv_rev]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))
      (add unsafe 50% (by nlinarith [mul_inv_self]))
      (add unsafe 50% (by nlinarith [inv_mul_self]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))
      (add unsafe 50% (by nlinarith [mul_right_inv]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_fst_of_isTwoCocycle]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_of_isMulOneCocycle]))
      (add unsafe 50% (by nlinarith [groupCohomology.twoCocycles_map_one_fst]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_fst_of_isMulTwoCocycle]))
      (add unsafe 50% (by nlinarith [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add unsafe 50% (by nlinarith [groupCohomology.twoCocycles_map_one_snd]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_of_isOneCocycle]))
      (add unsafe 50% (by nlinarith [mul_eq_one_iff_eq_inv]))
      (add unsafe 50% (by nlinarith [commutatorElement_def]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_iff_eq_mul]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_inv_of_isMulOneCocycle]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_snd_of_isTwoCocycle]))
      (add unsafe 50% (by nlinarith [mul_inv_cancel_left]))
      (add unsafe 50% (by nlinarith [inv_mul_eq_one]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_inv_of_isOneCocycle]))
      (add unsafe 50% (by nlinarith [inv_eq_iff_mul_eq_one]))
      (add unsafe 50% (by nlinarith [MulAut.conj_inv_apply]))
      (add unsafe 50% (by nlinarith [MulAut.conj_apply]))
      (add unsafe 50% (by nlinarith [inv_mul_cancel_left]))
      (add unsafe 50% (by nlinarith [IsGroupHom.one_iff_ker_inv]))
      (add unsafe 50% (by nlinarith [MulAut.conj]))
      (add unsafe 50% (by nlinarith [MulAut.conj_symm_apply]))

  have h4 : b * a * (b * b⁻¹) = b * a * 1 := by
    -- Substitution using h3
    clear * - h3
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 16
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isMulTwoCocycle]))
      (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add norm 0 (by grind only [mul_left_inj]))
      (add norm 0 (by grind only [add_self]))
      (add norm 0 (by grind only [mul_right_inj]))
      (add norm 0 (by grind only [CategoryTheory.PresheafOfGroups.Cochain₀.inv_apply]))
      (add norm 0 (by grind only [conj_mul]))
      (add norm 0 (by grind only [AddChar.mulShift_apply]))
      (add norm 0 (by grind only [HNNExtension.equiv_symm_eq_conj]))
      (add norm 0 (by grind only [Equiv.Perm.sameCycle_conj]))
      (add norm 0 (by grind only [Equiv.Perm.cycleType_conj]))
      (add norm 0 (by grind only [Equiv.Perm.Disjoint.cycleType]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_fst_of_isTwoCocycle]))
      (add unsafe 50% (by nlinarith [mul_inv_self]))
      (add unsafe 50% (by nlinarith [groupCohomology.twoCocycles_map_one_fst]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [mul_right_inv]))
      (add unsafe 50% (by nlinarith [inv_mul_self]))
      (add unsafe 50% (by nlinarith [groupCohomology.twoCocycles_map_one_snd]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
      (add unsafe 50% (by nlinarith [mul_inv_cancel_left]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_iff_eq_mul]))
      (add unsafe 50% (by nlinarith [commutatorElement_def]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_of_isMulOneCocycle]))
      (add unsafe 50% (by nlinarith [inv_mul_cancel_left]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_snd_of_isTwoCocycle]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))

  have h5 : b * a * 1 = b * a := by
    -- Identity property
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 16
      enableSimp := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isMulTwoCocycle]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [add_self]))
      (add norm 0 (by grind only [DualNumber.snd_eps]))
      (add norm 0 (by grind only [LaurentPolynomial.T_zero]))
      (add norm 0 (by grind only [AddChar.mulShift_apply]))
      (add norm 0 (by grind only [mul_right_inj]))
      (add norm 0 (by grind only [gronwallBound_ε0]))
      (add norm 0 (by grind only [mul_left_inj]))
      (add norm 0 (by grind only [IsLprojection.mul_compl_self]))
      (add norm 0 (by grind only [FractionalIdeal.dual_eq_mul_inv]))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [CochainComplex.mappingCone.fst]))
      (add norm 0 (by grind only [CochainComplex.mappingCone.inl]))
      (add norm 0 (by grind only [LaurentPolynomial.T_add]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_fst_of_isTwoCocycle]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [groupCohomology.twoCocycles_map_one_fst]))
      (add unsafe 50% (by nlinarith [mul_inv_self]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))
      (add unsafe 50% (by nlinarith [AddChar.one_apply]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
      (add unsafe 50% (by nlinarith [groupCohomology.twoCocycles_map_one_snd]))
      (add unsafe 50% (by nlinarith [mul_right_inv]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_of_isMulOneCocycle]))
      (add unsafe 50% (by nlinarith [inv_mul_self]))
      (add unsafe 50% (by nlinarith [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_snd_of_isTwoCocycle]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_of_isOneCocycle]))

  have h6 : b * a = b * a := by
    -- Transitivity from h1 through h5
    clear * - h1 h2 h4 h5
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_self]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isMulTwoCocycle]))
      (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isTwoCocycle]))
      (add norm 0 (by grind only [mul_left_inj]))
      (add norm 0 (by grind only [mul_right_inj]))
      (add norm 0 (by grind only [groupCohomology.twoCocycles_map_one_fst]))
      (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [groupCohomology.twoCocycles_map_one_snd]))
      (add norm 0 (by grind only [AddChar.mulShift_apply]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [HNNExtension.equiv_symm_eq_conj]))
      (add norm 0 (by grind only [add_self]))
      (add norm 0 (by grind only [mul_inv_cancel_left]))
      (add norm 0 (by grind only [inv_mul_self]))
      (add norm 0 (by grind only [conj_mul]))
      (add norm 0 (by grind only [Equiv.Perm.sameCycle_conj]))
      (add norm 0 (by grind only [eq_inv_mul_iff_mul_eq]))
      (add norm 0 (by grind only [FractionalIdeal.dual_eq_mul_inv]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [mul_inv_self]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_iff_eq_mul]))
      (add unsafe 50% (by nlinarith [mul_right_inv]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
      (add unsafe 50% (by nlinarith [commutatorElement_def]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_of_isMulOneCocycle]))

  -- Now we need to show that b * a = g * a * b * g⁻¹ where g = b
  -- i.e., b * a = b * a * b * b⁻¹
  -- Which we've shown above
  have h7 : b * a = g * a * b * g⁻¹ := by
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 16
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [conj_mul]))
      (add norm 0 (by grind only [mul_inv_eq_iff_eq_mul]))
      (add norm 0 (by grind only [mul_inv_rev]))
      (add norm 0 (by grind only [mul_inv_cancel_left]))
      (add norm 0 (by grind only [Equiv.Perm.sameCycle_conj]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add norm 0 (by grind only [eq_inv_mul_iff_mul_eq]))
      (add norm 0 (by grind only [Equiv.Perm.cycleType_conj]))
      (add norm 0 (by grind only [HNNExtension.equiv_symm_eq_conj]))
      (add norm 0 (by grind only [eq_mul_inv_iff_mul_eq]))
      (add norm 0 (by grind only [inv_mul_cancel_left]))
      (add norm 0 (by grind only [commutatorElement_def]))
      (add norm 0 (by grind only [Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub]))
      (add norm 0 (by grind only [inv_mul_eq_iff_eq_mul]))
      (add norm 0 (by grind only [Equiv.Perm.SameCycle.conj]))
      (add norm 0 (by grind only [Equiv.Perm.Disjoint.cycleType]))
      (add norm 0 (by grind only [CategoryTheory.PresheafOfGroups.Cochain₀.inv_apply]))
      (add norm 0 (by grind only [mul_inv_cancel_right]))
      (add norm 0 (by grind only [Equiv.Perm.card_support_conj]))
      (add norm 0 (by grind only [Subgroup.MemLeftTransversals.inv_mul_toFun_mem]))
      (add norm 0 (by grind only [groupCohomology.twoCocycles_map_one_fst]))
      (add norm 0 (by grind only [Subgroup.coe_inv]))
      (add norm 0 (by grind only [Subgroup.coe_mul]))
      (add norm 0 (by grind only [eq_inv_mul_of_mul_eq]))
      (add norm 0 (by grind only [HNNExtension.equiv_eq_conj]))
      (add norm 0 (by grind only [MulAut.conj]))
      (add unsafe 50% (by nlinarith [mul_inv_self]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))
      (add unsafe 50% (by nlinarith [MulAut.conj_inv_apply]))
      (add unsafe 50% (by nlinarith [mul_right_inv]))
      (add unsafe 50% (by nlinarith [MulAut.conj_apply]))

  use g
  -- exact h7
