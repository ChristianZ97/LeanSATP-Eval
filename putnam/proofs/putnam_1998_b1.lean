
import Mathlib
open Set Function Metric

set_option maxHeartbeats 0

abbrev putnam_1998_b1_solution : ℝ := 6

theorem putnam_1998_b1
: sInf {((x + 1/x)^6 - (x^6 + 1/x^6) - 2)/((x + 1/x)^3 + (x^3 + 1/x^3)) | x > (0 : ℝ)} = putnam_1998_b1_solution := by
  have h_u_ge_2 : ∀ (x : ℝ), x > (0:ℝ) → x + (1:ℝ)/x ≥ (2:ℝ) := by
    clear * -
    simp_all only [gt_iff_lt, one_div, ge_iff_le]
    refine' fun x hx => le_of_sub_nonneg _
    simp_all only [sub_nonneg]
    field_simp [hx.ne.symm, hx.ne']
    rw [le_div_iff (hx)] <;> nlinarith [sq_nonneg (x - 1)]

  have h_cube_identity : ∀ (x : ℝ), x ≠ (0:ℝ) → x^3 + (1:ℝ)/x^3 = (x + (1:ℝ)/x)^3 - 3*(x + (1:ℝ)/x) := by
    clear * -
    intro x a
    simp_all only [ne_eq, one_div]
    (field_simp)
    (nlinarith)

  have h_sixth_power_identity : ∀ (x : ℝ), x ≠ (0:ℝ) → x^6 + (1:ℝ)/x^6 = (x^3 + (1:ℝ)/x^3)^2 - (2:ℝ) := by
    clear * -
    intro x a
    simp_all only [ne_eq, one_div]
    (field_simp)
    (nlinarith)

  have h_sixth_expanded : ∀ (x : ℝ), x ≠ (0:ℝ) → x^6 + (1:ℝ)/x^6 = ((x + (1:ℝ)/x)^3 - 3*(x + (1:ℝ)/x))^2 - (2:ℝ) := by
    clear * - h_sixth_power_identity h_cube_identity
    intro x a
    simp_all only [ne_eq, one_div, not_false_eq_true]

  have h_num_factor : ∀ (u : ℝ), u^6 - (((u^3 - 3*u)^2 - 2) : ℝ) - 2 = 3*u^2*(2*u^2 - 3) := by
    clear * -
    intro u
    (nlinarith)

  have h_denom_factor : ∀ (u : ℝ), u^3 + (u^3 - 3*u) = u*(2*u^2 - 3) := by
    clear * -
    intro u
    (nlinarith)

  have h_denom_positive : ∀ (u : ℝ), u ≥ (2:ℝ) → 2*u^2 - 3 > (0:ℝ) := by
    clear * -
    intro u a
    simp_all only [ge_iff_le, gt_iff_lt, sub_pos]
    (nlinarith)

  have h_f_simplified : ∀ (x : ℝ), x > (0:ℝ) →
    ((x + (1:ℝ)/x)^6 - (x^6 + (1:ℝ)/x^6) - 2)/((x + (1:ℝ)/x)^3 + (x^3 + (1:ℝ)/x^3)) =
    3*(x + (1:ℝ)/x) := by
    clear * - h_u_ge_2 h_cube_identity h_sixth_expanded h_num_factor h_denom_factor h_denom_positive
    intro x a
    simp_all only [gt_iff_lt, one_div, ge_iff_le, ne_eq, sub_pos]
    (field_simp)
    (nlinarith)

  have h_lower_bound : ∀ (x : ℝ), x > (0:ℝ) →
    ((x + (1:ℝ)/x)^6 - (x^6 + (1:ℝ)/x^6) - 2)/((x + (1:ℝ)/x)^3 + (x^3 + (1:ℝ)/x^3)) ≥ (6:ℝ) := by
    clear * - h_u_ge_2 h_f_simplified
    simp_all only [gt_iff_lt, one_div, ge_iff_le]
    exact fun x hx => by linarith [h_u_ge_2 x hx]

  have h_inf_eq_6 : sInf {((x + (1:ℝ)/x)^6 - (x^6 + (1:ℝ)/x^6) - 2)/((x + (1:ℝ)/x)^3 + (x^3 + (1:ℝ)/x^3)) | x > (0:ℝ)} = (6:ℝ) := by
    clear * - h_lower_bound
    simp_all only [gt_iff_lt, one_div, ge_iff_le]
    apply le_antisymm
    · have h_ub := h_lower_bound 1 (by norm_num)
      simp_all only [inv_one, one_pow, ge_iff_le]
      refine csInf_le ?_ ?_
      · use 6
        norm_num at h_ub ⊢
        simp_all only
        simp (config := { contextual := true }) [lowerBounds, h_lower_bound]
      · simp_all only [mem_setOf_eq]
        refine ⟨1, by positivity, ?_⟩ <;> norm_num
    · apply le_csInf
      · exact ⟨6, by exact ⟨1, by norm_num, by norm_num⟩⟩
      · simp_all only [mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true]

  have h_final : sInf {((x + 1/x)^6 - (x^6 + 1/x^6) - 2)/((x + 1/x)^3 + (x^3 + 1/x^3)) | x > (0 : ℝ)} = putnam_1998_b1_solution := by
    clear * - h_inf_eq_6
    simp_all only [gt_iff_lt, one_div]

  exact h_final
