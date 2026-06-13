import Mathlib
open BigOperators Real Nat Topology Rat
/-- What is the units digit of the sum of the squares of the first nine positive integers? Show that it is 5.-/

theorem mathd_numbertheory_3 : (∑ x in Finset.range 10, (x + 1) ^ 2) % 10 = 5 := by

    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
  })
    (add safe 1 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by exfalso))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply FiberBundle.extChartAt_target | rw [FiberBundle.extChartAt_target] | simp only [FiberBundle.extChartAt_target]))
    (add unsafe 30% (by first | apply MeasureTheory.setAverage_congr_fun | rw [MeasureTheory.setAverage_congr_fun] | simp only [MeasureTheory.setAverage_congr_fun]))
    (add unsafe 30% (by first | apply Ordinal.nadd_lt_nadd_of_lt_of_le | rw [Ordinal.nadd_lt_nadd_of_lt_of_le] | simp only [Ordinal.nadd_lt_nadd_of_lt_of_le]))
    (add unsafe 30% (by first | apply Ordnode.merge_nil_right | rw [Ordnode.merge_nil_right] | simp only [Ordnode.merge_nil_right]))