
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
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_inv_d_eq_sum : (1:ℝ) / d = (1:ℝ) / (a + b + c) := by
      clear * - h_sum h_sum_ne_zero
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_cases : a + b = 0 ∨ b + c = 0 ∨ c + a = 0 := by
      clear * - h_prod
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

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

    have h_sys : a + b + c = d ∧ (1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c = (1:ℝ) / d := by
      clear * - h_sum h_inv_d_eq
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
      (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    exact h_sys

  · -- Direction 2: System implies Solution
    intro h_sys
    cases' h_sys with h_sum h_inv
    have h_sum_ne_zero : a + b + c ≠ 0 := by
      clear * - h_sum hd
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_sub : (1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c = (1:ℝ) / (a + b + c) := by
      clear * - h_sum h_inv h_sum_ne_zero
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_prod_ne_zero : a * b * c ≠ 0 := by
      clear * - ha hb hc
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_comb_frac : (a * b + b * c + c * a) / (a * b * c) = (1:ℝ) / (a + b + c) := by
      clear * - ha hb hc h_sub
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_cross : (a * b + b * c + c * a) * (a + b + c) = a * b * c := by
      clear * - ha hb hc hd h_comb_frac h_prod_ne_zero h_sum_ne_zero
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_exp : a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2 + 3 * a * b * c = a * b * c := by
      clear * - h_cross
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
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_simp : a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2 + 2 * a * b * c = 0 := by
      clear * - h_exp
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
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h_fact : (a + b) * (b + c) * (c + a) = 0 := by
      clear * - h_simp
      simp_all only [mul_eq_zero]
      simp [or_iff_not_imp_right, add_eq_zero_iff_eq_neg]
      intros X Y
      apply mul_right_cancel₀ (mul_ne_zero (sub_ne_zero_of_ne X) (sub_ne_zero_of_ne Y)) <;> nlinarith

    have h_sol : putnam_1977_a2_solution a b c d := by
      clear * - h_sum h_fact
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    exact h_sol
