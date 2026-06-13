import Mathlib
open BigOperators Real Nat Topology Rat
/-- My father's age is $1222_{3}$, in base three to represent his three lower limbs -- two legs and a cane.  How old is he in base ten? Show that it is 53.-/

theorem mathd_numbertheory_85 : 1 * 3 ^ 3 + 2 * 3 ^ 2 + 2 * 3 + 2 = 53 := by

    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
  })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
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
    (add unsafe 30% (by first | apply FiberBundle.extChartAt_target | rw [FiberBundle.extChartAt_target] | simp only [FiberBundle.extChartAt_target]))
    (add unsafe 30% (by first | apply MeasureTheory.Memℒp.smul | rw [MeasureTheory.Memℒp.smul] | simp only [MeasureTheory.Memℒp.smul]))
    (add unsafe 30% (by first | apply MeasureTheory.Memℒp.smul_of_top_right | rw [MeasureTheory.Memℒp.smul_of_top_right] | simp only [MeasureTheory.Memℒp.smul_of_top_right]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Set.subset_insert_iff_of_not_mem | rw [Set.subset_insert_iff_of_not_mem] | simp only [Set.subset_insert_iff_of_not_mem]))