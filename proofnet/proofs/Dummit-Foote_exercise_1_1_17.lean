
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  -- Step 1: x^n = 1, since the order of x is n
  have h1 : x ^ (n : ℕ) = 1 := by
    clear * - hxn
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 100 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by norm_num))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [pow_orderOf_eq_one]))
      (add norm 0 (by grind only [DihedralGroup.r_one_pow]))
      (add norm 0 (by grind only [DihedralGroup.orderOf_r_one]))
      (add norm 0 (by rw [DihedralGroup.r_one_pow_n]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow]))
      (add norm 0 (by grind only [orderOf_dvd_iff_pow_eq_one]))
      (add norm 0 (by grind only [pow_eq_pow_iff_modEq]))
      (add norm 0 (by grind only [ZMod.pow_totient]))
      (add norm 0 (by grind only [orderOf_units]))
      (add norm 0 (by grind only [orderOf_pos]))
      (add norm 0 (by grind only [AddChar.zmodChar_apply]))
      (add norm 0 (by grind only [ModularCyclotomicCharacter.toFun_spec]))
      (add norm 0 (by grind only [orderOf_dvd_of_pow_eq_one]))
      (add norm 0 (by grind only [pow_card_eq_one']))
      (add norm 0 (by grind only [orderOf]))
      (add norm 0 (by grind only [rootsOfUnity.coe_pow]))
      (add norm 0 (by grind only [IsPrimitiveRoot.eq_orderOf]))
      (add norm 0 (by grind only [Subgroup.orderOf_coe]))
      (add norm 0 (by grind only [orderOf_one]))
      (add norm 0 (by grind only [DihedralGroup.orderOf_r]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [pow_card_eq_one]))
      (add norm 0 (by grind only [orderOf_dvd_natCard]))
      (add norm 0 (by grind only [orderOf_dvd_iff_zpow_eq_one]))
      (add norm 0 (by grind only [QuaternionGroup.orderOf_a_one]))
      (add norm 0 (by grind only [orderOf_dvd_card]))
      (add norm 0 (by grind only [ModularCyclotomicCharacter.toFun_spec']))
      (add norm 0 (by grind only [QuaternionGroup.one_def]))
      (add norm 0 (by grind only [QuaternionGroup.orderOf_xa]))
      (add norm 0 (by grind only [zpow_pow_orderOf]))
      (add norm 0 (by grind only [MulAction.period_dvd_orderOf]))
      (add safe 0 (by simp_all [MulAction.pow_smul_eq_iff_period_dvd]))

  -- Step 2: n = 1 + (n - 1), where n is at least 1 (since n : ℕ+)
  have h2 : (n : ℕ) = 1 + ((n : ℕ) - 1) := by
    clear * -
    symm
    zify
    simp

  -- Step 3: x^n = x^(1 + (n - 1))
  have h3 : x ^ (n : ℕ) = x ^ (1 + ((n : ℕ) - 1)) := by
    clear * - h2
    rw [← h2]

  -- Step 4: x^(1 + (n - 1)) = x^1 * x^(n - 1)
  have h4 : x ^ (1 + ((n : ℕ) - 1)) = x ^ 1 * x ^ ((n : ℕ) - 1) := by
    clear * -
    rw [pow_add]

  -- Step 5: x^1 * x^(n - 1) = x * x^(n - 1)
  have h5 : x ^ 1 * x ^ ((n : ℕ) - 1) = x * x ^ ((n : ℕ) - 1) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 100 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [zpow_add]))
      (add norm 0 (by grind only [Matrix.zpow_add]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [zpow_one]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by rw [AddConstMapClass.map_add_zsmul]))
      (add norm 0 (by grind only [Matrix.zpow_add_one]))
      (add norm 0 (by grind only [zpow_add_one]))
      (add norm 0 (by grind only [zpow_add₀]))
      (add norm 0 (by grind only [Matrix.zpow_add_of_nonneg]))
      (add norm 0 (by grind only [zpow_sub]))
      (add norm 0 (by grind only [pow_one]))
      (add norm 0 (by grind only [one_zpow]))
      (add norm 0 (by grind only [Real.rpow_add_int]))
      (add norm 0 (by grind only [Pell.d]))
      (add norm 0 (by rw [Zsqrtd.intCast_val]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [zpow_mul']))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [ppow_one]))
      (add norm 0 (by grind only [zpow_add_one₀]))
      (add norm 0 (by grind only [Int.induction_on]))
      (add norm 0 (by grind only [Int.sub_eq_add_neg]))
      (add norm 0 (by grind only [Int.add_assoc]))
      (add norm 0 (by grind only [mul_zpow]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [Int.mul_add]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by rw [mul_self]))

  -- Step 6: x * x^(n - 1) = 1
  have h6 : x * x ^ ((n : ℕ) - 1) = 1 := by
    clear * - h1 h3 h4 h5
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 100 (by gcongr))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [pow_one]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow]))
      (add norm 0 (by grind only [DihedralGroup.one_def]))
      (add norm 0 (by grind only [DihedralGroup.r_one_pow_n]))
      (add norm 0 (by grind only [zpow_add]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [QuaternionGroup.one_def]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [ppow_one]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [PerfectClosure.one_def]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [zpow_one]))
      (add norm 0 (by grind only [DihedralGroup.r_one_pow]))
      (add norm 0 (by grind only [FiniteField.pow_card_sub_one_eq_one]))
      (add norm 0 (by grind only [mul_left_inj]))
      (add norm 0 (by grind only [div_inv_eq_mul]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [geom_sum₂_with_one]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [Commute.one_right]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
      (add norm 0 (by grind only [pow_zero]))

  -- Step 7: Multiply both sides by x⁻¹ from the left
  have h7 : x⁻¹ * (x * x ^ ((n : ℕ) - 1)) = x⁻¹ * 1 := by
    clear * - h6
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableSimp := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isTwoCocycle]))
      (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isMulTwoCocycle]))
      (add norm 0 (by grind only [mul_inv_rev]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [mul_left_inj]))
      (add norm 0 (by grind only [mul_right_inj]))
      (add norm 0 (by grind only [inner_]))
      (add norm 0 (by grind only [groupCohomology.twoCocycles_map_one_fst]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [LaurentPolynomial.T_zero]))
      (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add norm 0 (by grind only [inv_mul_self]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [FractionalIdeal.dual_eq_mul_inv]))
      (add norm 0 (by grind only [DualNumber.snd_eps]))
      (add norm 0 (by grind only [AddChar.mulShift_apply]))
      (add norm 0 (by grind only [mul_inv_cancel_left]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [groupCohomology.twoCocycles_map_one_snd]))
      (add norm 0 (by grind only [mul_inv]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [mul_right_inv]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
      (add unsafe 50% (by nlinarith [mul_inv_self]))
      (add unsafe 50% (by nlinarith [AddChar.one_apply]))

  -- Step 8: Associativity: (x⁻¹ * x) * x^(n - 1) = x⁻¹ * 1
  have h8 : (x⁻¹ * x) * x ^ ((n : ℕ) - 1) = x⁻¹ * 1 := by
    clear * - h7
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 512
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
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_inv_rev]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_left_inj]))
      (add norm 0 (by grind only [commutatorElement_def]))
      (add norm 0 (by grind only [mul_right_inj]))
      (add norm 0 (by grind only [conj_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
      (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add norm 0 (by grind only [mul_inv_eq_iff_eq_mul]))
      (add norm 0 (by grind only [Subgroup.coe_inv]))
      (add norm 0 (by grind only [mul_inv_cancel_left]))
      (add norm 0 (by grind only [mul_neg]))
      (add norm 0 (by grind only [mul_inv_cancel_right]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [HNNExtension.equiv_symm_eq_conj]))
      (add norm 0 (by grind only [InvMemClass.coe_inv]))
      (add norm 0 (by grind only [CategoryTheory.PresheafOfGroups.Cochain₀.inv_apply]))
      (add norm 0 (by grind only [inv_mul_cancel_left]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
      (add unsafe 50% (by nlinarith [mul_inv_self]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))
      (add unsafe 50% (by nlinarith [mul_right_inv]))

  -- Step 9: 1 * x^(n - 1) = x⁻¹
  have h9 : 1 * x ^ ((n : ℕ) - 1) = x⁻¹ := by
    clear * - h8
    have h10 : x⁻¹ * x = 1 := by group
    rw [h10] at h8
    rw [h8]
    rw [mul_one]

  -- Step 10: x^(n - 1) = x⁻¹
  have h10 : x ^ ((n : ℕ) - 1) = x⁻¹ := by
    clear * - h9
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by gcongr))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [mul_inv_rev]))
      (add norm 0 (by grind only [inner_]))
      (add norm 0 (by grind only [inv_mul']))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [InvMemClass.coe_inv]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [LaurentPolynomial.T_zero]))
      (add norm 0 (by grind only [zpow_add]))
      (add norm 0 (by grind only [Pell.Solution₁.x_inv]))
      (add norm 0 (by grind only [mul_neg]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by grind only [mul_left_inj]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [zpow_add₀]))
      (add norm 0 (by grind only [CategoryTheory.PresheafOfGroups.Cochain₀.inv_apply]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_fst_of_isTwoCocycle]))
      (add unsafe 50% (by nlinarith [mul_right_inv]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_fst_of_isMulTwoCocycle]))
      (add unsafe 50% (by nlinarith [inv_mul_self]))
      (add unsafe 50% (by nlinarith [mul_inv_self]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))
      (add unsafe 50% (by nlinarith [groupCohomology.map_one_of_isMulOneCocycle]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [groupCohomology.twoCocycles_map_one_fst]))
      (add unsafe 50% (by nlinarith [groupCohomology.twoCocycles_map_one_snd]))

  -- Step 11: Conclusion
  -- exact h10
  exact id (Eq.symm h10)
