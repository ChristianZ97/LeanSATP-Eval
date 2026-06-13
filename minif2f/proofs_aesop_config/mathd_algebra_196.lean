import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    (∑ k in S, k) = 4 := by
  have h_abs_prop : ∀ x : ℝ, abs ((2:ℝ) - x) = 3 ↔ (2:ℝ) - x = 3 ∨ (2:ℝ) - x = (-3:ℝ) := by
    clear * -
    rintro a <;> simp [abs_eq]

  have h_case1_equiv : ∀ x : ℝ, (2:ℝ) - x = 3 ↔ x = (-1:ℝ) := by
    clear * -
    aesop
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_num [*] at *))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply AffineSubspace.left_mem_perpBisector | rw [AffineSubspace.left_mem_perpBisector] | simp only [AffineSubspace.left_mem_perpBisector]))
    (add unsafe 30% (by first | apply AffineSubspace.right_mem_perpBisector | rw [AffineSubspace.right_mem_perpBisector] | simp only [AffineSubspace.right_mem_perpBisector]))
    (add unsafe 30% (by first | apply Real.Angle.toReal_eq_pi_div_two_iff | rw [Real.Angle.toReal_eq_pi_div_two_iff] | simp only [Real.Angle.toReal_eq_pi_div_two_iff]))
    (add unsafe 30% (by first | apply Real.Angle.toReal_eq_pi_iff | rw [Real.Angle.toReal_eq_pi_iff] | simp only [Real.Angle.toReal_eq_pi_iff]))
    (add unsafe 30% (by first | apply Real.Angle.toReal_inj | rw [Real.Angle.toReal_inj] | simp only [Real.Angle.toReal_inj]))
    (add unsafe 10% (by first | apply NumberField.RingOfIntegers.eq_iff | rw [NumberField.RingOfIntegers.eq_iff] | simp only [NumberField.RingOfIntegers.eq_iff]))
    (add unsafe 10% (by first | apply PMF.ext_iff | rw [PMF.ext_iff] | simp only [PMF.ext_iff]))

  have h_case2_equiv : ∀ x : ℝ, (2:ℝ) - x = (-3:ℝ) ↔ x = (5:ℝ) := by
    clear * -
    aesop (config := {
    maxNormIterations       := 140
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Orientation.rotation_eq_self_iff | rw [Orientation.rotation_eq_self_iff] | simp only [Orientation.rotation_eq_self_iff]))
    (add unsafe 30% (by first | apply Real.neg_pi_div_two_eq_arcsin | rw [Real.neg_pi_div_two_eq_arcsin] | simp only [Real.neg_pi_div_two_eq_arcsin]))
    (add unsafe 30% (by first | apply eq_comm | rw [eq_comm] | simp only [eq_comm]))
    (add unsafe 30% (by first | apply inv_smul_eq_iff | rw [inv_smul_eq_iff] | simp only [inv_smul_eq_iff]))
    (add unsafe 30% (by first | apply smul_right_inj | rw [smul_right_inj] | simp only [smul_right_inj]))
    (add unsafe 10% (by first | apply Real.Angle.toReal_eq_pi_div_two_iff | rw [Real.Angle.toReal_eq_pi_div_two_iff] | simp only [Real.Angle.toReal_eq_pi_div_two_iff]))
    (add unsafe 10% (by first | apply div_eq_iff_eq_mul' | rw [div_eq_iff_eq_mul'] | simp only [div_eq_iff_eq_mul']))
    (add unsafe 10% (by first | apply smul_eq_iff_eq_inv_smul | rw [smul_eq_iff_eq_inv_smul] | simp only [smul_eq_iff_eq_inv_smul]))

  have h_member_iff : ∀ x : ℝ, x ∈ S ↔ x = (-1:ℝ) ∨ x = (5:ℝ) := by
    clear * - h₀ h_abs_prop h_case1_equiv h_case2_equiv
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

  have h_neg1_root : abs ((2:ℝ) - (-1:ℝ)) = 3 := by
    clear * -
    aesop (config := {
    maxRuleApplications     := 260
    maxGoals                := 64
    enableUnfold            := false
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by exfalso))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by omega))
    (add unsafe 10% (by first | apply ArithmeticFunction.abs_moebius_eq_one_of_squarefree | rw [ArithmeticFunction.abs_moebius_eq_one_of_squarefree] | simp only [ArithmeticFunction.abs_moebius_eq_one_of_squarefree]))
    (add unsafe 10% (by first | apply Nat.abs_cast | rw [Nat.abs_cast] | simp only [Nat.abs_cast]))
    (add unsafe 10% (by first | apply abs_one | rw [abs_one] | simp only [abs_one]))
    (add unsafe 10% (by first | apply mabs_inv | rw [mabs_inv] | simp only [mabs_inv]))
    (add unsafe 10% (by first | apply mabs_mabs | rw [mabs_mabs] | simp only [mabs_mabs]))

  have h_neg1_in_S : (-1:ℝ) ∈ S := by
    clear * - h₀ h_neg1_root
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

  have h_5_root : abs ((2:ℝ) - (5:ℝ)) = 3 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    enableUnfold            := false
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by exfalso))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply abs_one | rw [abs_one] | simp only [abs_one]))
    (add unsafe 10% (by first | apply Nat.abs_cast | rw [Nat.abs_cast] | simp only [Nat.abs_cast]))
    (add unsafe 10% (by first | apply mabs_inv | rw [mabs_inv] | simp only [mabs_inv]))
    (add unsafe 10% (by first | apply mabs_mabs | rw [mabs_mabs] | simp only [mabs_mabs]))

  have h_5_in_S : (5:ℝ) ∈ S := by
    clear * - h₀ h_5_root
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

  have h_S_is_finite_set : S = {(-1:ℝ), (5:ℝ)} := by
    clear * - h_member_iff h_neg1_in_S h_5_in_S
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

  have h_sum_substitution : (∑ k in S, k) = (∑ k in {(-1:ℝ), (5:ℝ)}, k) := by
    clear * - h_S_is_finite_set
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

  have h_sum_expansion : (∑ k in {(-1:ℝ), (5:ℝ)}, k) = ((-1:ℝ) + (5:ℝ)) := by
    clear * -
    repeat erw [Finset.sum_insert] <;> simp
    norm_num

  have h_final_addition : ((-1:ℝ) + (5:ℝ)) = 4 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    })
    (add safe 1 (by field_simp))
    (add safe 2 (by ring))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by simp))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply Int.negOnePow_neg | rw [Int.negOnePow_neg] | simp only [Int.negOnePow_neg]))
    (add unsafe 30% (by first | apply Int.negOnePow_one | rw [Int.negOnePow_one] | simp only [Int.negOnePow_one]))
    (add unsafe 30% (by first | apply Int.negOnePow_succ | rw [Int.negOnePow_succ] | simp only [Int.negOnePow_succ]))

  have h_final_result : (∑ k in S, k) = 4 := by
    clear * - h_sum_substitution h_sum_expansion h_final_addition
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

  exact h_final_result
