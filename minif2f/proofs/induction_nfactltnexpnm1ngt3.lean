import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  have h_step1 : (3 : ℕ) ! = 3 * 2 * 1 := by
    clear * -
    simp_all only [reduceMul, mul_one]
    rfl

  have h_step2 : 3 * 2 * 1 = 6 := by
    clear * -
    simp_all only [reduceMul, mul_one]

  have h_step3 : (3 : ℕ) ^ (3 - 1) = 3 ^ 2 := by
    clear * -
    simp_all only [Nat.add_one_sub_one, reducePow]

  have h_step4 : (3 : ℕ) ^ 2 = 9 := by
    clear * -
    aesop
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 40% (by first | apply QuaternionGroup.xa_sq | rw [QuaternionGroup.xa_sq] | simp only [QuaternionGroup.xa_sq]))
    (add unsafe 40% (by first | apply Real.rpow_two | rw [Real.rpow_two] | simp only [Real.rpow_two]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
    (add unsafe 10% (by first | apply CoxeterSystem.simple_sq | rw [CoxeterSystem.simple_sq] | simp only [CoxeterSystem.simple_sq]))
    (add unsafe 10% (by first | apply mul_pow | rw [mul_pow] | simp only [mul_pow]))
    (add unsafe 10% (by first | apply sq_sub_sq | rw [sq_sub_sq] | simp only [sq_sub_sq]))

  have h_step5 : (3 : ℕ) ! < (3 : ℕ) ^ (3 - 1) := by
    clear * - h_step1 h_step2 h_step3 h_step4
    simp_all only [reduceMul, mul_one, Nat.add_one_sub_one, reducePow, reduceLT]

  have h_step_inductive : ∀ (k : ℕ), 3 ≤ k → k ! < k ^ (k - 1) → (k + 1) ! < (k + 1) ^ ((k + 1) - 1) := by
    intro k hk IH
    have h_step6 : 3 ≤ k := hk
    have h_step7 : k ! < k ^ (k - 1) := IH
    have h_step8 : (k + 1) ! = (k + 1) * k ! := by
      clear * -
      rfl

    have h_step9 : (k + 1) * k ! < (k + 1) * k ^ (k - 1) := by
      clear * - h_step7
      simp_all only [add_pos_iff, lt_one_iff, pos_of_gt, or_true, mul_lt_mul_left]

    have h_step10 : k < k + 1 := by
      clear * -
      simp_all only [lt_add_iff_pos_right, lt_one_iff, pos_of_gt]

    have h_step11 : k - 1 ≥ 2 := by
      clear * - h_step6
      simp_all only [ge_iff_le]
      (omega)

    have h_step12 : k - 1 > 0 := by
      clear * - h_step11
      simp_all only [ge_iff_le, gt_iff_lt, tsub_pos_iff_lt]
      (omega)

    have h_step13 : k ^ (k - 1) < (k + 1) ^ (k - 1) := by
      clear * - h_step10 h_step12
      simp_all only [lt_add_iff_pos_right, lt_one_iff, pos_of_gt, gt_iff_lt, tsub_pos_iff_lt]
      (gcongr)
      · simp_all only [ne_eq]
        apply Aesop.BuiltinRules.not_intro
        intro a
        (omega)
      · simp_all only [lt_add_iff_pos_right, lt_one_iff, pos_of_gt]

    have h_step14 : (k + 1) * k ^ (k - 1) < (k + 1) * (k + 1) ^ (k - 1) := by
      clear * - h_step13
      simp_all only [add_pos_iff, lt_one_iff, pos_of_gt, or_true, mul_lt_mul_left]

    have h_step15 : (k + 1) * (k + 1) ^ (k - 1) = (k + 1) ^ (1 + k - 1) := by
      clear * -
      simp_all only [add_tsub_cancel_left]
      cases k <;> simp
      ring

    have h_step16 : 1 + k - 1 = k := by
      clear * -
      simp_all only [add_tsub_cancel_left]

    have h_step17 : (k + 1) ^ (1 + k - 1) = (k + 1) ^ k := by
      clear * - h_step16
      simp_all only [add_tsub_cancel_left]

    have h_step18 : (k + 1) * k ^ (k - 1) < (k + 1) ^ k := by
      clear * - h_step14 h_step15 h_step17
      simp_all only [add_tsub_cancel_left]

    have h_step19 : (k + 1) ! < (k + 1) ^ k := by
      clear * - h_step8 h_step9 h_step18
      simp_all only [add_pos_iff, lt_one_iff, pos_of_gt, or_true, mul_lt_mul_left]
      (nlinarith)

    have h_step20 : (k + 1) ^ k = (k + 1) ^ ((k + 1) - 1) := by
      clear * -
      simp_all only [add_tsub_cancel_right]

    have h_ind_final : (k + 1) ! < (k + 1) ^ ((k + 1) - 1) := by
      clear * - h_step19 h_step20
      simp_all only [add_tsub_cancel_right]

    exact h_ind_final

  simp_all only [reduceMul, mul_one, Nat.add_one_sub_one, reducePow, reduceLT, add_tsub_cancel_right, gt_iff_lt]
  revert n
  intros n h_base
  induction h_base <;> simp_all [factorial, pow_succ]
