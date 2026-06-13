
import Mathlib

set_option maxHeartbeats 0

theorem putnam_1987_a1
(A B C D : Set (ℝ × ℝ))
(hA : A = {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≠ 0 ∧ x ^ 2 - y ^ 2 = x / (x ^ 2 + y ^ 2)})
(hB : B = {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≠ 0 ∧ 2 * x * y + y / (x ^ 2 + y ^ 2) = 3})
(hC : C = {(x, y) : ℝ × ℝ | x ^ 3 - 3 * x * y ^ 2 + 3 * y = 1})
(hD : D = {(x, y) : ℝ × ℝ | 3 * x ^ 2 * y - 3 * x - y ^ 3 = 0})
: A ∩ B = C ∩ D := by
  have h_equiv : ∀ (x y : ℝ), ((x, y) ∈ A ∩ B) ↔ ((x, y) ∈ C ∩ D) := by
    intro x y
    simp only [hA, hB, hC, hD, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · -- Forward direction: (x,y) ∈ A ∩ B implies (x,y) ∈ C ∩ D
      intro hAB
      have h_sum_neq_zero : (x:ℝ) ^ 2 + (y:ℝ) ^ 2 ≠ (0:ℝ) := by
        clear * - hAB
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

      have h_real_part_orig : (x:ℝ) ^ 2 - (y:ℝ) ^ 2 = (x:ℝ) / ((x:ℝ) ^ 2 + (y:ℝ) ^ 2) := by
        clear * - hAB
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
        (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_imag_part_orig : 2 * (x:ℝ) * (y:ℝ) + (y:ℝ) / ((x:ℝ) ^ 2 + (y:ℝ) ^ 2) = (3:ℝ) := by
        clear * - hAB
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
        (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_sum_rewrite : (x:ℝ) ^ 2 + (y:ℝ) ^ 2 = (x:ℝ) ^ 2 + (y:ℝ) ^ 2 := by
        clear * -
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
        (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_reciprocal_form : ((x:ℝ):ℝ) / ((x:ℝ) ^ 2 + (y:ℝ) ^ 2) - ((-y:ℝ):ℝ) / ((x:ℝ) ^ 2 + (y:ℝ) ^ 2) * (0:ℝ) = (x:ℝ) / ((x:ℝ) ^ 2 + (y:ℝ) ^ 2) := by
        clear * -
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
        (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
        (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_combined_step : ((x:ℝ) ^ 2 - (y:ℝ) ^ 2) + (2 * (x:ℝ) * (y:ℝ)) * (0:ℝ) = (x:ℝ) / ((x:ℝ) ^ 2 + (y:ℝ) ^ 2) := by
        clear * - h_real_part_orig
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
        (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_key_equation : (x:ℝ) ^ 3 - 3 * (x:ℝ) * (y:ℝ) ^ 2 = (1:ℝ) - 3 * (y:ℝ) := by
        clear * - h_sum_neq_zero h_real_part_orig h_imag_part_orig
        simp_all only [ne_eq]
        field_simp [mul_comm] at * <;> ring
        apply mul_right_cancel₀ h_sum_neq_zero <;> nlinarith [pow_two_nonneg (x - 1), pow_two_nonneg (y - 1)]

      have h_imag_key_equation : 3 * (x:ℝ) ^ 2 * (y:ℝ) - (y:ℝ) ^ 3 = 3 * (x:ℝ) := by
        clear * - h_sum_neq_zero h_real_part_orig h_imag_part_orig
        simp_all only [ne_eq]
        try field_simp [h_sum_neq_zero] at *
        simp_all only
        nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (2 * x * y - 1), sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg (x - 1),
          sq_nonneg (y - 1)]

      have h_C_condition : (x:ℝ) ^ 3 - 3 * (x:ℝ) * (y:ℝ) ^ 2 + 3 * (y:ℝ) = (1:ℝ) := by
        clear * - h_key_equation
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
        (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_D_condition : 3 * (x:ℝ) ^ 2 * (y:ℝ) - 3 * (x:ℝ) - (y:ℝ) ^ 3 = (0:ℝ) := by
        clear * - h_imag_key_equation
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

      constructor
      · exact h_C_condition
      · exact h_D_condition

    · -- Backward direction: (x,y) ∈ C ∩ D implies (x,y) ∈ A ∩ B
      intro hCD
      have h_C_eq : (x:ℝ) ^ 3 - 3 * (x:ℝ) * (y:ℝ) ^ 2 + 3 * (y:ℝ) = (1:ℝ) := by
        clear * - hCD
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

      have h_D_eq : 3 * (x:ℝ) ^ 2 * (y:ℝ) - 3 * (x:ℝ) - (y:ℝ) ^ 3 = (0:ℝ) := by
        clear * - hCD
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

      have h_cube_expansion_real : (x:ℝ) ^ 3 - 3 * (x:ℝ) * (y:ℝ) ^ 2 = (x:ℝ) ^ 3 - 3 * (x:ℝ) * (y:ℝ) ^ 2 := by
        clear * -
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

      have h_cube_expansion_imag : 3 * (x:ℝ) ^ 2 * (y:ℝ) - (y:ℝ) ^ 3 = 3 * (x:ℝ) ^ 2 * (y:ℝ) - (y:ℝ) ^ 3 := by
        clear * -
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

      have h_sum_pos_or_zero : (x:ℝ) ^ 2 + (y:ℝ) ^ 2 ≥ (0:ℝ) := by
        clear * -
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
        (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_not_both_zero : ¬((x:ℝ) = (0:ℝ) ∧ (y:ℝ) = (0:ℝ)) := by
        clear * - h_C_eq h_D_eq
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

      have h_sum_nonzero_backward : (x:ℝ) ^ 2 + (y:ℝ) ^ 2 ≠ (0:ℝ) := by
        clear * - h_not_both_zero h_sum_pos_or_zero
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

      have h_x_squared_minus_y_squared : (x:ℝ) ^ 2 - (y:ℝ) ^ 2 = (x:ℝ) / ((x:ℝ) ^ 2 + (y:ℝ) ^ 2) := by
        clear * - h_C_eq h_D_eq h_sum_nonzero_backward
        simp_all only [ne_eq]
        field_simp [h_sum_nonzero_backward, mul_comm]
        try nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + y)]

      have h_2xy_plus_term : 2 * (x:ℝ) * (y:ℝ) + (y:ℝ) / ((x:ℝ) ^ 2 + (y:ℝ) ^ 2) = (3:ℝ) := by
        clear * - h_C_eq h_D_eq h_sum_nonzero_backward
        simp_all only [ne_eq]
        field_simp [h_sum_nonzero_backward] <;> ring
        nlinarith [mul_self_nonneg (x - y), mul_self_nonneg (x + 1), mul_self_nonneg (y + 1)]

      constructor
      · constructor
        · exact h_sum_nonzero_backward
        · exact h_x_squared_minus_y_squared

      · constructor
        · exact h_sum_nonzero_backward
        · exact h_2xy_plus_term

  have h_set_ext : A ∩ B = C ∩ D := by
    apply Set.ext
    intro p
    simp only [Set.mem_inter_iff]
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

  exact h_set_ext
