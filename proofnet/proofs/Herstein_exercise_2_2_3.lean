
import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  simp only [hP] at hn hn1 hn2
  -- Let's work with arbitrary elements a and b
  intro a b
  -- Step 1: From P(n+1), we have (ab)^(n+1) = a^(n+1) * b^(n+1)
  have h_step1 : (a*b)^(n+1) = a^(n+1) * b^(n+1) := by
    clear * - hn1
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 100 (by gcongr))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [pow_succ]))
      (add norm 0 (by grind only [pow_succ']))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [gold_pow_sub_gold_pow]))
      (add norm 0 (by grind only [wittPolynomial_zmod_self]))
      (add norm 0 (by grind only [Nat.pow_succ']))
      (add norm 0 (by grind only [IsNilpotent.pow_succ]))
      (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux2]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [PerfectClosure.mk_pow]))
      (add norm 0 (by grind only [Polynomial.expand_mul]))
      (add norm 0 (by grind only [Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [neg_pow]))
      (add norm 0 (by grind only [Matrix.zpow_add_one]))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux4]))
      (add norm 0 (by grind only [LinearMap.iterate_succ]))
      (add norm 0 (by grind only [ppow_add]))
      (add norm 0 (by grind only [Commute.mul_pow]))
      (add norm 0 (by grind only [Perfection.coeff_pow_p]))
      (add norm 0 (by grind only [Polynomial.derivative_pow_succ]))
      (add norm 0 (by grind only [Commute.pow_left]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Polynomial.expand_expand]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_pow_iff]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))
      (add norm 0 (by grind only [mul_inv_rev]))
      (add norm 0 (by grind only [Commute.pow_self]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_pow_mul_iff]))

  -- Step 2: Expand (ab)^(n+1) as (ab)^n * (ab)
  have h_step2 : (a*b)^n * (a*b) = a^(n+1) * b^(n+1) := by
    clear * - h_step1
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 100 (by gcongr))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [pow_succ]))
      (add norm 0 (by grind only [pow_succ']))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Nat.pow_succ']))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux2]))
      (add norm 0 (by grind only [gold_pow_sub_gold_pow]))
      (add norm 0 (by grind only [wittPolynomial_zmod_self]))
      (add norm 0 (by grind only [IsNilpotent.pow_succ]))
      (add norm 0 (by grind only [PerfectClosure.mk_pow]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_pow_mul_iff]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [ppow_add]))
      (add norm 0 (by grind only [Polynomial.expand_mul]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_pow_iff]))
      (add norm 0 (by grind only [LinearMap.iterate_succ]))
      (add norm 0 (by grind only [Matrix.zpow_add_one]))
      (add norm 0 (by grind only [Commute.mul_pow]))
      (add norm 0 (by grind only [GradedMonoid.fst_pow]))
      (add norm 0 (by grind only [MvPolynomial.NewtonIdentities.esymm_to_weight]))
      (add norm 0 (by grind only [WittVector.map_frobeniusPoly.key₂]))
      (add norm 0 (by grind only [Polynomial.derivative_pow_succ]))
      (add norm 0 (by grind only [neg_pow]))
      (add norm 0 (by grind only [Perfection.coeff_pow_p]))
      (add norm 0 (by grind only [Commute.pow_left]))

  -- Step 3: From P(n), we have (ab)^n = a^n * b^n, so substitute
  have h_step3 : a^n * b^n * a * b = a^(n+1) * b^(n+1) := by
    have h_ab_n : (a*b)^n = a^n * b^n := by
      clear * - hn
      aesop (config := {
        maxRuleApplications := 40
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 100 (by gcongr))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [pow_mul]))
        (add norm 0 (by grind only [QuotientGroup.mk_pow]))
        (add norm 0 (by grind only [Subgroup.coe_pow]))
        (add norm 0 (by grind only [FiniteField.pow_card_pow]))
        (add norm 0 (by grind only [CircleDeg1Lift.translationNumber_pow]))
        (add norm 0 (by grind only [FiniteField.pow_card]))
        (add norm 0 (by grind only [neg_pow]))
        (add norm 0 (by grind only [AddChar.pow_apply]))
        (add norm 0 (by grind only [QuotientGroup.eq]))
        (add norm 0 (by grind only [FiniteField.pow_card_sub_one_eq_one]))
        (add norm 0 (by grind only [rootsOfUnity.coe_pow]))
        (add norm 0 (by grind only [QuotientGroup.eq_one_iff]))
        (add norm 0 (by grind only [AddChar.coe_pow]))
        (add norm 0 (by grind only [ModularCyclotomicCharacter.toFun_spec]))
        (add norm 0 (by grind only [QuotientGroup.mk_mul]))
        (add norm 0 (by grind only [Commute.mul_pow]))
        (add norm 0 (by grind only [neg_one_sq]))
        (add norm 0 (by grind only [npow_mul]))
        (add norm 0 (by grind only [mul_inv_eq_iff_eq_mul]))
        (add norm 0 (by grind only [SemiconjBy.pow_right]))
        (add norm 0 (by grind only [QuaternionAlgebra.coe_pow]))
        (add norm 0 (by grind only [pow_mul']))
        (add norm 0 (by grind only [MulAut.conj_apply]))
        (add norm 0 (by grind only [mul_pow]))
        (add norm 0 (by grind only [commutatorElement_def]))
        (add norm 0 (by grind only [Eq.trans]))
        (add norm 0 (by grind only [groupCohomology.mem_twoCocycles_iff]))
        (add norm 0 (by grind only [pow_card_eq_one']))
        (add norm 0 (by grind only [Subgroup.coe_mul]))
        (add unsafe 50% (by nlinarith [mul_inv_eq_one]))
        (add unsafe 50% (by nlinarith [groupCohomology.mem_oneCocycles_iff]))
        (add unsafe 50% (by nlinarith [groupCohomology.map_one_of_isMulOneCocycle]))

    clear * - h_step2 h_ab_n
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [pow_succ]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [pow_succ']))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Nat.pow_succ']))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux2]))
      (add norm 0 (by grind only [PerfectClosure.mk_pow]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_pow_mul_iff]))
      (add norm 0 (by grind only [gold_pow_sub_gold_pow]))
      (add norm 0 (by grind only [IsNilpotent.pow_succ]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [wittPolynomial_zmod_self]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_pow_iff]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [MvPolynomial.NewtonIdentities.esymm_to_weight]))
      (add norm 0 (by grind only [ppow_add]))
      (add norm 0 (by grind only [Polynomial.expand_mul]))
      (add norm 0 (by grind only [Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one]))
      (add norm 0 (by grind only [Commute.mul_pow]))
      (add norm 0 (by grind only [GradedMonoid.fst_pow]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.gaussSum_frob_iter]))
      (add norm 0 (by grind only [Matrix.zpow_add_one]))
      (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux4]))
      (add norm 0 (by grind only [WittVector.map_frobeniusPoly.key₂]))
      (add norm 0 (by grind only [LinearMap.iterate_succ]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.gaussSum_frob]))
      (add norm 0 (by grind only [AddChar.pow_mulShift]))

  -- Step 4: Simplify a^(n+1) = a^n * a and b^(n+1) = b^n * b on RHS
  -- So we have a^n * b^n * a * b = a^n * a * b^n * b
  -- Cancel a^n from left and b from right to get b^n * a * b = a * b^n * b
  -- Actually, let's be more careful. We want to derive b^n * a = a * b^n
  -- From a^n * b^n * a * b = a^n * a * b^n * b
  -- Multiply both sides on the left by (a^n)⁻¹ and on the right by b⁻¹
  -- This gives b^n * a = a * b^n
  have h_step5 : b^n * a = a * b^n := by
    have h_rhs_expand : a^(n+1) * b^(n+1) = a^n * a * b^n * b := by
      simp [pow_succ, mul_assoc]

    have h_eq : a^n * b^n * a * b = a^n * a * b^n * b := by
      rw [h_step3, h_rhs_expand]

    -- Multiply both sides by (a^n)⁻¹ on the left
    have h_left_cancel : b^n * a * b = a * b^n * b := by
      calc
        b^n * a * b = (a^n : G)⁻¹ * (a^n * b^n * a * b) := by simp [mul_assoc]
        _ = (a^n : G)⁻¹ * (a^n * a * b^n * b) := by rw [h_eq]
        _ = a * b^n * b := by simp [mul_assoc, inv_mul_cancel_left]

    -- Now multiply both sides by b⁻¹ on the right
    calc
      b^n * a = b^n * a * b * b⁻¹ := by simp [mul_assoc]
      _ = a * b^n * b * b⁻¹ := by rw [h_left_cancel]
      _ = a * b^n := by simp [mul_assoc]

  -- Step 6-10: Similarly use P(n+2) to get b^(n+1) * a = a * b^(n+1)
  have h_step7 : (a*b)^(n+2) = a^(n+2) * b^(n+2) := by
    clear * - hn2
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 100 (by gcongr))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [pow_succ]))
      (add norm 0 (by grind only [pow_succ']))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux2]))
      (add norm 0 (by grind only [gold_pow_sub_gold_pow]))
      (add norm 0 (by grind only [wittPolynomial_zmod_self]))
      (add norm 0 (by grind only [PerfectClosure.mk_pow]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Nat.pow_succ']))
      (add norm 0 (by grind only [IsNilpotent.pow_succ]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [neg_pow]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Polynomial.expand_mul]))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by grind only [Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one]))
      (add norm 0 (by grind only [Matrix.zpow_add_one]))
      (add norm 0 (by grind only [Commute.mul_pow]))
      (add norm 0 (by grind only [ppow_add]))
      (add norm 0 (by grind only [MvPolynomial.NewtonIdentities.esymm_to_weight]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.gaussSum_frob_iter]))
      (add norm 0 (by grind only [FiniteField.pow_card_pow]))
      (add norm 0 (by grind only [GradedMonoid.fst_pow]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux4]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.gaussSum_frob]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [Perfection.coeff_pow_p]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_pow_iff]))

  have h_step8 : (a*b)^(n+1) * (a*b) = a^(n+2) * b^(n+2) := by
    clear * - h_step7
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [pow_succ]))
      (add norm 0 (by grind only [pow_succ']))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [Nat.pow_succ']))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [gold_pow_sub_gold_pow]))
      (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux2]))
      (add norm 0 (by grind only [wittPolynomial_zmod_self]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [IsNilpotent.pow_succ]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Matrix.zpow_add_one]))
      (add norm 0 (by grind only [PerfectClosure.mk_pow]))
      (add norm 0 (by grind only [LinearMap.iterate_succ]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_pow_mul_iff]))
      (add norm 0 (by grind only [conj_mul]))
      (add norm 0 (by grind only [ppow_add]))
      (add norm 0 (by grind only [Polynomial.expand_mul]))
      (add norm 0 (by grind only [Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one]))
      (add norm 0 (by grind only [Polynomial.derivative_pow_succ]))
      (add norm 0 (by grind only [mul_inv_rev]))
      (add norm 0 (by grind only [WittVector.map_frobeniusPoly.key₂]))
      (add norm 0 (by grind only [MvPolynomial.NewtonIdentities.esymm_to_weight]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_pow_iff]))
      (add norm 0 (by grind only [WittVector.verschiebung_coeff_succ]))
      (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux4]))
      (add norm 0 (by grind only [Perfection.coeff_pow_p]))

  have h_step9 : a^(n+1) * b^(n+1) * a * b = a^(n+2) * b^(n+2) := by
    have h_ab_n1 : (a*b)^(n+1) = a^(n+1) * b^(n+1) := by
      clear * - hn1
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 380
        maxNormIterations := 320
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 100 (by gcongr))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 100 (by exfalso))
        (add norm 100 (by ring_nf at *))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by simp))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [pow_succ]))
        (add norm 0 (by grind only [pow_succ']))
        (add norm 0 (by grind only [pow_add]))
        (add norm 0 (by grind only [gold_pow_sub_gold_pow]))
        (add norm 0 (by grind only [wittPolynomial_zmod_self]))
        (add norm 0 (by grind only [Nat.pow_succ']))
        (add norm 0 (by grind only [IsNilpotent.pow_succ]))
        (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux2]))
        (add norm 0 (by grind only [mul_assoc]))
        (add norm 0 (by grind only [pow_mul]))
        (add norm 0 (by grind only [PerfectClosure.mk_pow]))
        (add norm 0 (by grind only [Polynomial.expand_mul]))
        (add norm 0 (by grind only [Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one]))
        (add norm 0 (by grind only [mul_pow]))
        (add norm 0 (by grind only [neg_pow]))
        (add norm 0 (by grind only [Matrix.zpow_add_one]))
        (add norm 0 (by grind only [LucasLehmer.X.ω]))
        (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
        (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux4]))
        (add norm 0 (by grind only [LinearMap.iterate_succ]))
        (add norm 0 (by grind only [ppow_add]))
        (add norm 0 (by grind only [Commute.mul_pow]))
        (add norm 0 (by grind only [Perfection.coeff_pow_p]))
        (add norm 0 (by grind only [Polynomial.derivative_pow_succ]))
        (add norm 0 (by grind only [Commute.pow_left]))
        (add norm 0 (by grind only [mul_left_comm]))
        (add norm 0 (by grind only [Polynomial.expand_expand]))
        (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_pow_iff]))
        (add norm 0 (by grind only [LucasLehmer.X.ωb]))
        (add norm 0 (by grind only [mul_inv_rev]))
        (add norm 0 (by grind only [Commute.pow_self]))
        (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_pow_mul_iff]))

    have h_rhs_expand : a^(n+2) * b^(n+2) = a^(n+1) * a * b^(n+1) * b := by
      simp [pow_succ, mul_assoc]

    have h_lhs_eq : a^(n+1) * b^(n+1) * a * b = a^(n+1) * b^(n+1) * a * b := rfl
    rw [h_ab_n1] at h_step8
    rw [h_rhs_expand] at h_step8
    rw [h_rhs_expand]
    rw [← h_rhs_expand]
    rw [h_lhs_eq]
    rw [h_rhs_expand]
    rw [← h_step8]
    group

  have h_step10 : b^(n+1) * a = a * b^(n+1) := by
    have h_rhs_expand : a^(n+2) * b^(n+2) = a^(n+1) * a * b^(n+1) * b := by
      simp [pow_succ, mul_assoc]

    have h_eq : a^(n+1) * b^(n+1) * a * b = a^(n+1) * a * b^(n+1) * b := by
      rw [h_step9, h_rhs_expand]

    -- Multiply both sides by (a^(n+1))⁻¹ on the left
    have h_left_cancel : b^(n+1) * a * b = a * b^(n+1) * b := by
      calc
        b^(n+1) * a * b = (a^(n+1) : G)⁻¹ * (a^(n+1) * b^(n+1) * a * b) := by simp [mul_assoc]
        _ = (a^(n+1) : G)⁻¹ * (a^(n+1) * a * b^(n+1) * b) := by rw [h_eq]
        _ = a * b^(n+1) * b := by simp [mul_assoc, inv_mul_cancel_left]

    -- Now multiply both sides by b⁻¹ on the right
    calc
      b^(n+1) * a = b^(n+1) * a * b * b⁻¹ := by simp [mul_assoc]
      _ = a * b^(n+1) * b * b⁻¹ := by rw [h_left_cancel]
      _ = a * b^(n+1) := by simp [mul_assoc]

  -- Step 11-13: Use h_step5 and h_step10 to show ba = ab
  -- From h_step5: b^n * a = a * b^n
  -- From h_step10: b^(n+1) * a = a * b^(n+1)
  -- Note that b^(n+1) = b^n * b
  -- So b^n * b * a = a * b^n * b
  -- But also b^n * b * a = b^n * (b * a)
  -- And a * b^n * b = (a * b^n) * b
  -- From h_step5, a * b^n = b^n * a, so (a * b^n) * b = b^n * a * b
  -- So b^n * (b * a) = b^n * (a * b)
  -- Cancel b^n from the left to get b * a = a * b
  have h_ba_eq_ab : b * a = a * b := by
    calc
      b * a = (b^n : G)⁻¹ * (b^n * b * a) := by simp [mul_assoc, inv_mul_cancel_left]
      _ = (b^n : G)⁻¹ * (b^(n+1) * a) := by simp [pow_succ, mul_assoc]
      _ = (b^n : G)⁻¹ * (a * b^(n+1)) := by rw [h_step10]
      _ = (b^n : G)⁻¹ * (a * b^n * b) := by simp [pow_succ, mul_assoc]
      _ = (b^n : G)⁻¹ * (b^n * a * b) := by
        have h_a_bn_eq_bn_a : a * b^n = b^n * a := by
          rw [h_step5]

        rw [h_a_bn_eq_bn_a]
        <;> simp [mul_assoc]

      _ = a * b := by simp [mul_assoc, inv_mul_cancel_left]

  -- exact h_ba_eq_ab
  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 20
    maxNormIterations := 60
    maxGoals := 512
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by exfalso))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [mul_assoc]))
    (add norm 0 (by grind only [mul_left_comm]))
    (add norm 0 (by grind only [mul_comm]))
    (add norm 0 (by grind only [mul_right_comm]))
    (add norm 0 (by grind only [pow_add]))
    (add norm 0 (by grind only [pow_succ]))
    (add norm 0 (by grind only [Nat.pow_succ']))
    (add norm 0 (by grind only [Nat.succ_mul]))
    (add norm 0 (by grind only [pow_succ']))
    (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_pow_mul_iff]))
    (add norm 0 (by grind only [conj_mul]))
    (add norm 0 (by grind only [Subgroup.coe_mul]))
    (add norm 0 (by grind only [HNNExtension.equiv_symm_eq_conj]))
    (add norm 0 (by grind only [Subgroup.IsComplement.equiv_fst_eq_mul_inv]))
    (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
    (add norm 0 (by grind only [mul_inv_rev]))
    (add norm 0 (by grind only [mul_inv_eq_iff_eq_mul]))
    (add norm 0 (by grind only [Equiv.Perm.sameCycle_conj]))
    (add norm 0 (by grind only [eq_inv_mul_iff_mul_eq]))
    (add norm 0 (by grind only [eq_mul_inv_iff_mul_eq]))
    (add norm 0 (by grind only [Subgroup.IsComplement.equiv_snd_eq_inv_mul]))
    (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_pow_iff]))
    (add norm 0 (by grind only [mul_left_inj]))
    (add norm 0 (by grind only [Nat.mul_succ]))
    (add norm 0 (by grind only [HNNExtension.equiv_eq_conj]))
    (add norm 0 (by grind only [mul_right_inj]))
    (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [commutatorElement_def]))
    (add norm 0 (by grind only [Equiv.Perm.Disjoint.cycleType]))
    (add norm 0 (by grind only [Zsqrtd.sqLe_smul]))
    (add norm 0 (by grind only [mul_mul_mul_comm]))
