import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem algebra_others_exirrpowirrrat : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
  let a : ℝ := Real.sqrt 2
  have h_a_irr : Irrational a := by
    clear * -
    simp_all only [a]
    apply irrational_sqrt_two

  have h_a_pos : (0 : ℝ) < a := by
    clear * -
    simp only [Real.sqrt_pos, ofNat_pos, a] at *

  let x : ℝ := a ^ a
  let y : ℝ := x ^ a
  have h_step5 : y = (a ^ a) ^ a := by
    clear * -
    simp_all only [y, x, a]

  have h_step6 : (a ^ a) ^ a = a ^ (a * a) := by
    clear * -
    simp_all only [ofNat_nonneg, mul_self_sqrt, rpow_two, sq_sqrt, a]
    simp [← Real.rpow_mul, a]

  have h_step7 : y = a ^ (a * a) := by
    clear * - h_step5 h_step6
    simp_all only [ofNat_nonneg, mul_self_sqrt, rpow_two, sq_sqrt, y, x, a]

  have h_step8 : a * a = (2 : ℝ) := by
    clear * -
    simp_all only [ofNat_nonneg, mul_self_sqrt, a]

  have h_step9 : y = (2 : ℝ) := by
    clear * - h_step7 h_step8
    simp_all only [ofNat_nonneg, mul_self_sqrt, rpow_two, sq_sqrt, y, x, a]

  have h_step10 : ¬Irrational ((2 : ℝ)) := by
    clear * -
    simp_all only [not_irrational_ofNat, not_false_eq_true]

  have h_y_rat : ¬Irrational y := by
    clear * - h_step9 h_step10
    simp_all only [not_irrational_ofNat, not_false_eq_true, y, x, a]

  have h_step11 : Irrational x ∨ ¬Irrational x := by
    clear * -
    simp_all only [x, a]
    apply em

  have h_case1 : ¬Irrational x → (∃ a' b', Irrational a' ∧ Irrational b' ∧ ¬Irrational (a' ^ b')) := by
    intro hx_not_irr
    have h_witness1 : Irrational a ∧ Irrational a ∧ ¬Irrational (a ^ a) := by
      clear * - h_a_irr hx_not_irr
      simp_all only [not_false_eq_true, and_self, a, x]

    clear * - h_witness1
    simp_all only [and_self_left, exists_and_left, a]
    obtain ⟨left, right⟩ := h_witness1
    (bound )

  have h_case2 : Irrational x → (∃ a' b', Irrational a' ∧ Irrational b' ∧ ¬Irrational (a' ^ b')) := by
    intro hx_irr
    have h_witness2 : Irrational x ∧ Irrational a ∧ ¬Irrational (x ^ a) := by
      clear * - hx_irr h_a_irr h_y_rat
      simp_all only [not_false_eq_true, and_self, a, x, y]

    clear * - h_witness2
    simp_all only [exists_and_left, x, a]
    obtain ⟨left, right⟩ := h_witness2
    obtain ⟨left_1, right⟩ := right
    (bound )

  have h_main : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
    clear * - h_step11 h_case1 h_case2
    simp_all only [exists_and_left, x, a]
    cases h_step11 with
    | inl h =>
    simp_all only [not_true_eq_false, not_isEmpty_of_nonempty, IsEmpty.exists_iff, and_true, implies_true, forall_const,
    x, a]
    | inr h_1 =>
    simp_all only [not_false_eq_true, forall_const, not_isEmpty_of_nonempty, IsEmpty.exists_iff, and_true, implies_true,
    x, a]

  exact h_main