import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have h1 : (27 : ℝ) = (3 : ℝ) ^ 3 := by
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
    (add unsafe 90% (by linarith))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Int.cast_two | rw [Int.cast_two] | simp only [Int.cast_two]))
    (add unsafe 30% (by first | apply Complex.cpow_two | rw [Complex.cpow_two] | simp only [Complex.cpow_two]))
    (add unsafe 30% (by first | apply Nat.factorial_two | rw [Nat.factorial_two] | simp only [Nat.factorial_two]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
    (add unsafe 10% (by first | apply Nat.cast_two | rw [Nat.cast_two] | simp only [Nat.cast_two]))

  have h2 : Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ 3) := by
    clear * - h1
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by split))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Set.subset_insert_iff_of_not_mem | rw [Set.subset_insert_iff_of_not_mem] | simp only [Set.subset_insert_iff_of_not_mem]))

  have h3 : Real.log ((3 : ℝ) ^ 3) = (3 : ℝ) * Real.log (3 : ℝ) := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply MeasureTheory.setAverage_congr_fun | rw [MeasureTheory.setAverage_congr_fun] | simp only [MeasureTheory.setAverage_congr_fun]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_le_of_lt | rw [Ordinal.nadd_lt_nadd_of_le_of_lt] | simp only [Ordinal.nadd_lt_nadd_of_le_of_lt]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_lt_of_le | rw [Ordinal.nadd_lt_nadd_of_lt_of_le] | simp only [Ordinal.nadd_lt_nadd_of_lt_of_le]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_right | rw [Ordinal.nadd_lt_nadd_right] | simp only [Ordinal.nadd_lt_nadd_right]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Set.subset_insert_iff_of_not_mem | rw [Set.subset_insert_iff_of_not_mem] | simp only [Set.subset_insert_iff_of_not_mem]))

  have h4 : Real.log (27 : ℝ) / Real.log (3 : ℝ) = ((3 : ℝ) * Real.log (3 : ℝ)) / Real.log (3 : ℝ) := by
    clear * - h2 h3
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
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
    (add unsafe 30% (by first | apply Ioo_mem_nhdsWithin_Iic | rw [Ioo_mem_nhdsWithin_Iic] | simp only [Ioo_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h5 : ((3 : ℝ) * Real.log (3 : ℝ)) / Real.log (3 : ℝ) = (3 : ℝ) := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_final : Real.log 27 / Real.log 3 = 3 := by
    clear * - h4 h5
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by split))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 80% (by norm_num [*] at *))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Or.resolve_left | rw [Or.resolve_left] | simp only [Or.resolve_left]))
    (add unsafe 30% (by first | apply Or.resolve_right | rw [Or.resolve_right] | simp only [Or.resolve_right]))
    (add unsafe 20% (by first | apply ne_of_gt | rw [ne_of_gt] | simp only [ne_of_gt]))
    (add unsafe 20% (by first | apply ne_of_lt | rw [ne_of_lt] | simp only [ne_of_lt]))
    (add unsafe 10% (by first | apply mt | rw [mt] | simp only [mt]))

  exact h_final
