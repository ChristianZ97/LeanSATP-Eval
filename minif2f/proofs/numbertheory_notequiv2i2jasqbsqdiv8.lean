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
    simp_all only [b]

  have h_step3 : a = 2 * 1 := by
    clear * - h_a_val
    simp_all only [mul_one, a]

  have h_step4 : b = 2 * 0 := by
    clear * - h_b_val
    simp_all only [mul_zero, b]

  have h_a_even : ∃ i : ℤ, a = 2 * i := by
    clear * - h_step3
    simp_all only [mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, left_eq_mul₀, exists_eq, a]

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
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, left_eq_mul₀, exists_eq, zero_eq_mul, false_or,
        exists_eq_right, a, b]

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
    simp_all only [Int.reducePow, mul_one, one_pow, a]

  have h_step7 : a ^ 2 = 4 * 1 := by
    clear * - h_step6
    simp_all only [Int.reducePow, one_pow, mul_one, a]

  have h_step8 : a ^ 2 = 4 := by
    clear * - h_step7
    simp only [Int.reducePow, mul_one, a] at *

  have h_step9 : b ^ 2 = (2 * 0) ^ 2 := by
    clear * - h_step4
    simp_all only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, b]

  have h_step10 : b ^ 2 = 2 ^ 2 * 0 ^ 2 := by
    clear * - h_step9
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Int.reducePow, b]

  have h_step11 : b ^ 2 = 4 * 0 := by
    clear * - h_step10
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Int.reducePow, mul_zero, b]

  have h_step12 : b ^ 2 = 0 := by
    clear * - h_step11
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, b]

  have h_step13 : a ^ 2 + b ^ 2 = 4 + 0 := by
    clear * - h_step8 h_step12
    simp_all only [Int.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, a, b]

  have h_step14 : a ^ 2 + b ^ 2 = 4 := by
    clear * - h_step13
    simp_all only [Int.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, a, b]

  have h_rhs_form : (∃ k : ℤ, a ^ 2 + b ^ 2 = 8 * k) ↔ (∃ k : ℤ, 4 = 8 * k) := by
    clear * - h_step14
    simp_all only [Int.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, a, b]

  have h_k_qcast : ∀ (k : ℤ), 4 = 8 * k → (k : ℚ) = (4 : ℚ) / 8 := by
    clear * -
    intro z hz
    field_simp [hz.symm]
    norm_cast <;> linarith

  have h_div_simple : (4 : ℚ) / 8 = (1 : ℚ) / 2 := by
    clear * -
    simp only [one_div] at *
    (ring)

  have h_k_is_half : ∀ (k : ℤ), 4 = 8 * k → (k : ℚ) = (1 : ℚ) / 2 := by
    clear * - h_k_qcast h_div_simple
    intro k a
    simp_all only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, one_div, forall_eq']

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
    simp_all only [one_div, ne_eq, not_exists, imp_false, not_false_eq_true, implies_true]

  have h_RHS_bot : ¬ (∃ k : ℤ, a ^ 2 + b ^ 2 = 8 * k) := by
    clear * - h_rhs_form h_step20_bot
    simp_all only [Int.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, not_exists,
        exists_const, a, b]

  have h_inst : (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
    clear * - h_univ h_a_val h_b_val
    simp_all [a, b]
    specialize h_univ a b <;> aesop

  have h_derive_RHS : ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
    clear * - h_inst h_LHS_top
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, left_eq_mul₀, zero_eq_mul, false_or, exists_eq_right,
        exists_eq, Int.reducePow, zero_pow, add_zero, true_iff, a, b]

  have h_contra : False := by
    clear * - h_derive_RHS h_RHS_bot
    simp_all only [Int.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, not_exists,
        exists_const, a, b]

  exact h_contra
