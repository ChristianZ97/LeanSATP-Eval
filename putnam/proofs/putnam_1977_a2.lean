
import Mathlib

set_option maxHeartbeats 0

abbrev putnam_1977_a2_solution : ℝ → ℝ → ℝ → ℝ → Prop :=
  fun a b c d => a + b + c = d ∧ (a + b) * (b + c) * (c + a) = 0

theorem putnam_1977_a2 :
    ∀ a b c d : ℝ,
      a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
        (putnam_1977_a2_solution a b c d ↔
          (a + b + c = d ∧ 1 / a + 1 / b + 1 / c = 1 / d)) := by
  intro a b c d ha hb hc hd
  constructor
  · -- Direction 1: Solution implies System
    intro h_sol
    cases' h_sol with h_sum h_prod
    have h_sum_ne_zero : a + b + c ≠ 0 := by
      clear * - h_sum hd
      subst h_sum
      simp_all only [ne_eq, not_false_eq_true]

    have h_inv_d_eq_sum : (1:ℝ) / d = (1:ℝ) / (a + b + c) := by
      clear * - h_sum h_sum_ne_zero
      subst h_sum
      simp_all only [ne_eq, one_div]

    have h_cases : a + b = 0 ∨ b + c = 0 ∨ c + a = 0 := by
      clear * - h_prod
      simp_all only [mul_eq_zero]
      cases h_prod with
      | inl h =>
        cases h with
        | inl h_1 => simp_all only [true_or]
        | inr h_2 => simp_all only [true_or, or_true]
      | inr h_1 => simp_all only [or_true]

    have h_inv_sum_eq : (1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c = (1:ℝ) / (a + b + c) := by
      clear * - ha hb hc h_cases
      simp_all only [ne_eq, one_div]
      rcases h_cases with (h | h | h) <;> field_simp [h] <;> ring
      · simp_all only [or_false]
        have : a = -b := by linarith
        simp_all only [neg_eq_zero, not_false_eq_true, neg_add_cancel, neg_mul, add_neg_cancel]
      · rw [add_eq_zero_iff_eq_neg] at h
        simp_all only [neg_eq_zero, not_false_eq_true, neg_mul, neg_add_cancel_comm]
        field_simp [ha, hc] <;> ring
      · field_simp [show c = -a from by linarith] <;> ring

    have h_inv_d_eq : (1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c = (1:ℝ) / d := by
      clear * - h_inv_sum_eq h_inv_d_eq_sum
      simp_all only [one_div, inv_inj]

    have h_sys : a + b + c = d ∧ (1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c = (1:ℝ) / d := by
      clear * - h_sum h_inv_d_eq
      subst h_sum
      simp_all only [one_div, and_self]

    exact h_sys

  · -- Direction 2: System implies Solution
    intro h_sys
    cases' h_sys with h_sum h_inv
    have h_sum_ne_zero : a + b + c ≠ 0 := by
      clear * - h_sum hd
      subst h_sum
      simp_all only [ne_eq, not_false_eq_true]

    have h_sub : (1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c = (1:ℝ) / (a + b + c) := by
      clear * - h_sum h_inv h_sum_ne_zero
      subst h_sum
      simp_all only [ne_eq, one_div]

    have h_prod_ne_zero : a * b * c ≠ 0 := by
      clear * - ha hb hc
      simp_all only [ne_eq, mul_eq_zero, or_self, not_false_eq_true]

    have h_comb_frac : (a * b + b * c + c * a) / (a * b * c) = (1:ℝ) / (a + b + c) := by
      clear * - ha hb hc h_sub
      simp_all only [ne_eq, one_div]
      (field_simp)
      (field_simp [*] at *)
      (nlinarith)

    have h_cross : (a * b + b * c + c * a) * (a + b + c) = a * b * c := by
      clear * - ha hb hc hd h_comb_frac h_prod_ne_zero h_sum_ne_zero
      simp_all only [ne_eq, mul_eq_zero, or_self, not_false_eq_true, one_div]
      (field_simp [*] at *)
      simp_all only

    have h_exp : a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2 + 3 * a * b * c = a * b * c := by
      clear * - h_cross
      (nlinarith)

    have h_simp : a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2 + 2 * a * b * c = 0 := by
      clear * - h_exp
      (nlinarith)

    have h_fact : (a + b) * (b + c) * (c + a) = 0 := by
      clear * - h_simp
      simp_all only [mul_eq_zero]
      simp [or_iff_not_imp_right, add_eq_zero_iff_eq_neg]
      intros X Y
      apply mul_right_cancel₀ (mul_ne_zero (sub_ne_zero_of_ne X) (sub_ne_zero_of_ne Y)) <;> nlinarith

    have h_sol : putnam_1977_a2_solution a b c d := by
      clear * - h_sum h_fact
      subst h_sum
      simp_all only [mul_eq_zero]
      cases h_fact with
      | inl h =>
        cases h with
        | inl h_1 =>
          simp_all only [zero_add]
          apply And.intro
          · simp_all only [zero_add]
          · simp_all only [zero_mul]
        | inr h_2 =>
          apply And.intro
          · simp_all only
          · simp_all only [mul_zero, zero_mul]
      | inr h_1 =>
        apply And.intro
        · simp_all only
        · simp_all only [mul_zero]

    exact h_sol
