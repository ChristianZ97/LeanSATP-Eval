import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem imo_1962_p2 (x : ℝ) (h₀ : 0 ≤ 3 - x) (h₁ : 0 ≤ x + 1)
    (h₂ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)) : -1 ≤ x ∧ x < 1 - Real.sqrt 31 / 8 := by
  have h_step_1 : Real.sqrt (3 - x) > Real.sqrt (x + 1) + (1:ℝ) / 2 := by
    clear * - h₂
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

  have h_step_2 : 3 - x > (Real.sqrt (x + 1) + (1:ℝ) / 2) ^ 2 := by
    clear * - h_step_1 h₀ h₁
    simp_all only [sub_nonneg, one_div, gt_iff_lt]
    have h_norm := h_step_1.le
    simp_all only [gt_iff_lt]
    rw [add_sq]
    simp_all only [sq_sqrt, inv_pow]
    nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 3 - x),
      Real.sq_sqrt (by linarith : (0 : ℝ) ≤ x + 1)]

  have h_step_3 : 3 - x > (x + 1) + Real.sqrt (x + 1) + ((1:ℝ) / 4) := by
    clear * - h_step_2
    simp_all only [one_div, gt_iff_lt]
    on_goal 1 => ring_nf at h_step_2 ⊢
    simp_all only [one_div]
    by_contra hcontra
    simp_all only [not_lt, tsub_le_iff_right]
    nlinarith [Real.sq_sqrt (show 1 + x ≥ 0 by nlinarith), Real.sqrt_nonneg (1 + x)]

  have h_step_4 : Real.sqrt (x + 1) < ((7:ℝ) / 4) - 2 * x := by
    clear * - h_step_3
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

  have h_step_5 : ((7:ℝ) / 4) - 2 * x ≥ 0 := by
    clear * - h_step_4 h₁
    simp_all only [ge_iff_le, sub_nonneg]
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x + 1), Real.sqrt_nonneg (x + 1)]

  have h_step_6 : x + 1 < (((7:ℝ) / 4) - 2 * x) ^ 2 := by
    clear * - h_step_4 h_step_5
    simp_all only [ge_iff_le, sub_nonneg]
    have h_lt := h_step_4
    simp_all only [gt_iff_lt]
    on_goal 1 => rw [Real.sqrt_lt' _] at h_lt
    · simp_all only
    · simp_all only [sub_pos]
      repeat' linarith [Real.sqrt_nonneg (x + 1), h_lt]

  have h_step_7 : 64 * x ^ 2 - 128 * x + 33 > 0 := by
    clear * - h_step_6
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

  have h_step_8 : x < 1 - Real.sqrt 31 / 8 ∨ x > 1 + Real.sqrt 31 / 8 := by
    clear * - h_step_7
    simp_all only [gt_iff_lt]
    rw [or_iff_not_imp_left]
    simp_all only [not_lt, tsub_le_iff_right]
    exact fun hx => by
      nlinarith [Real.sqrt_pos.2 (show (31 : ℝ) > 0 by norm_num), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 31)]

  have h_step_9 : x < 1 - Real.sqrt 31 / 8 := by
    clear * - h_step_8 h_step_5
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

  have h_step_10 : -1 ≤ x := by
    clear * - h₁
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

  exact ⟨h_step_10, h_step_9⟩
