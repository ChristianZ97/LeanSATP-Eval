import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_321 (n : ZMod 1399) (h₁ : n = 160⁻¹) : n = 1058 := by
  have h_step1 : (119 : ZMod 1399) = -((8 : ZMod 1399) * (160 : ZMod 1399)) := by
    clear * -
    rfl

  have h_step2 : (41 : ZMod 1399) = (160 : ZMod 1399) - (119 : ZMod 1399) := by
    clear * -
    rfl

  have h_step3 : (37 : ZMod 1399) = (119 : ZMod 1399) - ((2 : ZMod 1399) * (41 : ZMod 1399)) := by
    clear * -
    rfl

  have h_step4 : (4 : ZMod 1399) = (41 : ZMod 1399) - (37 : ZMod 1399) := by
    clear * -
    rfl

  have h_step5 : (1 : ZMod 1399) = (37 : ZMod 1399) - ((9 : ZMod 1399) * (4 : ZMod 1399)) := by
    clear * -
    rfl

  have h_inter1 : (1 : ZMod 1399) = ((10 : ZMod 1399) * (37 : ZMod 1399)) - ((9 : ZMod 1399) * (41 : ZMod 1399)) := by
    clear * - h_step4 h_step5
    simp_all only
    exact h_step5

  have h_inter2 : (1 : ZMod 1399) = ((10 : ZMod 1399) * (119 : ZMod 1399)) - ((29 : ZMod 1399) * (41 : ZMod 1399)) := by
    clear * - h_step3 h_inter1
    simp_all only
    exact h_inter1

  have h_inter3 : (1 : ZMod 1399) = ((39 : ZMod 1399) * (119 : ZMod 1399)) - ((29 : ZMod 1399) * (160 : ZMod 1399)) := by
    clear * - h_step2 h_inter2
    simp_all only
    exact h_inter2

  have h_euclid_res : (1 : ZMod 1399) = -((341 : ZMod 1399) * (160 : ZMod 1399)) := by
    clear * - h_step1 h_inter3
    simp_all only [mul_neg]
    exact h_inter3

  have h_coef_adjust : -((341 : ZMod 1399)) = (1058 : ZMod 1399) := by
    clear * -
    rfl

  have h_inverse_proof : (160 : ZMod 1399) * (1058 : ZMod 1399) = (1 : ZMod 1399) := by
    clear * - h_euclid_res h_coef_adjust
    simp_all only
    exact h_euclid_res

  have h_final : n = (1058 : ZMod 1399) := by
    clear * - h₁ h_inverse_proof
    simp_all only
    have h₂ : (160 : ZMod 1399) ≠ 0
    · simp_all only [ne_eq]
      decide
    · simp_all only [ne_eq]
      apply ZMod.inv_eq_of_mul_eq_one
      simp_all only

  exact h_final
