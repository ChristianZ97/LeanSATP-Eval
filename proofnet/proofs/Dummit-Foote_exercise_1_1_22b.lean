
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_1_1_22b {G: Type*} [Group G] (a b : G) :
  orderOf (a * b) = orderOf (b * a) := by
  -- Step 1: Show that conjugation relates (ab)^n and (ba)^n
  have h1 : ∀ n : ℕ, b * (a * b) ^ n * b⁻¹ = (b * a) ^ n := by
    clear * -
    intro n
    induction' n with k ih
    · simp
    · rw [pow_succ]
      rw [pow_succ]
      calc
        _ = b * (a * b) ^ k * b⁻¹ * (b * a) := by group
        _ = (b * a) ^ k * (b * a) := by rw [ih]

  -- Step 2: If (ab)^n = 1, then (ba)^n = 1
  have h2 : ∀ n : ℕ, (a * b) ^ n = 1 → (b * a) ^ n = 1 := by
    intro n hn
    have h3 : b * (a * b) ^ n * b⁻¹ = (b * a) ^ n := h1 n
    have h4 : b * 1 * b⁻¹ = (b * a) ^ n := by
      rw [hn] at h3
      exact h3

    have h5 : 1 = (b * a) ^ n := by
      simp at h4 ⊢
      <;> try simp_all [mul_assoc]

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
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_one]))
      (add norm 0 (by grind only [one_mul]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [mul_self]))
      (add norm 0 (by grind only [FractionalIdeal.count_pow]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by grind only [Commute.one_right]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [mul_left_inj]))
      (add norm 0 (by grind only [AddChar.one_apply]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))
      (add norm 0 (by grind only [NumberField.Units.coe_one]))
      (add norm 0 (by grind only [mul_right_inj]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isTwoCocycle]))
      (add norm 0 (by grind only [neg_pow]))
      (add norm 0 (by grind only [FiniteField.pow_card]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isMulTwoCocycle]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [FiniteField.pow_card_sub_one_eq_one]))
      (add norm 0 (by grind only [mul_left_eq_self]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))

  -- Step 3: If (ba)^n = 1, then (ab)^n = 1
  have h6 : ∀ n : ℕ, (b * a) ^ n = 1 → (a * b) ^ n = 1 := by
    intro n hn
    have h7 : a * (b * a) ^ n * a⁻¹ = (a * b) ^ n := by
      clear * -
      induction' n with n hn
      · simp
      · rw [pow_succ]
        rw [pow_succ]
        rw [← hn]
        group

    have h8 : a * 1 * a⁻¹ = (a * b) ^ n := by
      rw [hn] at h7
      exact h7

    have h9 : 1 = (a * b) ^ n := by
      simp at h8 ⊢
      <;> try simp_all [mul_assoc]

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
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_one]))
      (add norm 0 (by grind only [one_mul]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [FractionalIdeal.count_pow]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [mul_self]))
      (add norm 0 (by grind only [Commute.one_right]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [NumberField.Units.coe_one]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [neg_pow]))
      (add norm 0 (by grind only [AddChar.one_apply]))
      (add norm 0 (by grind only [FiniteField.pow_card]))
      (add norm 0 (by grind only [mul_left_inj]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow]))
      (add norm 0 (by grind only [FiniteField.pow_card_pow]))
      (add norm 0 (by grind only [mul_right_inj]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
      (add norm 0 (by grind only [mul_left_eq_self]))
      (add norm 0 (by grind only [FiniteField.pow_card_sub_one_eq_one]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))

  -- Step 4: The sets of positive integers k such that (ab)^k = 1 and (ba)^k = 1 are equal
  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 380
    maxNormIterations := 320
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by split))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [orderOf_pow]))
    (add norm 0 (by grind only [pow_orderOf_eq_one]))
    (add norm 0 (by grind only [orderOf]))
    (add norm 0 (by grind only [orderOf_pow']))
    (add norm 0 (by grind only [QuaternionGroup.orderOf_a]))
    (add norm 0 (by grind only [orderOf_dvd_iff_pow_eq_one]))
    (add norm 0 (by grind only [orderOf_dvd_of_pow_eq_one]))
    (add norm 0 (by grind only [orderOf_eq_prime_pow]))
    (add norm 0 (by grind only [QuaternionGroup.orderOf_xa]))
    (add norm 0 (by grind only [Commute.orderOf_mul_eq_mul_orderOf_of_coprime]))
    (add norm 0 (by grind only [IsPrimitiveRoot.eq_orderOf]))
    (add norm 0 (by grind only [DihedralGroup.orderOf_r]))
    (add norm 0 (by grind only [Equiv.Perm.Disjoint.orderOf]))
    (add norm 0 (by grind only [orderOf_eq_orderOf_iff]))
    (add norm 0 (by grind only [QuaternionGroup.orderOf_a_one]))
    (add norm 0 (by grind only [orderOf_eq_prime]))
    (add norm 0 (by grind only [ZMod.addOrderOf_coe]))
    (add norm 0 (by grind only [orderOf_le_of_pow_eq_one]))
    (add norm 0 (by grind only [DihedralGroup.orderOf_r_one]))
    (add norm 0 (by grind only [pow_mul]))
    (add norm 0 (by grind only [LucasLehmer.order_ω]))
    (add norm 0 (by grind only [orderOf_pow_orderOf_div]))
    (add norm 0 (by grind only [DihedralGroup.orderOf_sr]))
    (add norm 0 (by grind only [orderOf_pow_dvd]))
    (add norm 0 (by grind only [Subgroup.orderOf_coe]))
    (add norm 0 (by grind only [IsPrimitiveRoot.orderOf]))
    (add norm 0 (by grind only [approxOrderOf.image_pow_subset]))
    (add norm 0 (by grind only [orderOf_pow_of_dvd]))
    (add norm 0 (by grind only [orderOf_submonoid]))
    (add norm 0 (by grind only [AddCircle.addOrderOf_eq_pos_iff]))
    (add norm 0 (by grind only [MulAction.period_dvd_orderOf]))
    (add norm 0 (by grind only [DihedralGroup.r_one_pow]))
