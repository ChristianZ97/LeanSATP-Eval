import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators


theorem exercise_13_6_10 {K : Type*} [Field K] [Fintype Kˣ] :
  (∏ x : Kˣ,  x) = -1 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 100 (by exfalso))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 0 (by assumption_mod_cast))
    (add norm 0 (by grind only [Finset.prod_const_one]))
    (add norm 0 (by grind only [FiniteField.sum_pow_units]))
    (add norm 0 (by grind only [Finset.prod_singleton]))
    (add norm 0 (by grind only [Finset.prod_eq_zero]))
    (add norm 0 (by grind only [FiniteField.prod_univ_units_id_eq_neg_one]))
    (add norm 0 (by grind only [Finset.prod_eq_single]))
    (add norm 0 (by grind only [Finset.prod_eq_one]))
    (add norm 0 (by grind only [Finset.prod_erase]))
    (add norm 0 (by grind only [Finset.not_mem_erase]))
    (add norm 0 (by grind only [Finset.insert_erase]))
    (add norm 0 (by grind only [Finset.mul_prod_erase]))
    (add norm 0 (by grind only [IsKleinFour.eq_finset_univ]))
    (add norm 0 (by grind only [FiniteField.sum_pow_lt_card_sub_one]))
    (add norm 0 (by grind only [Finset.prod_eq_one_iff']))
    (add norm 0 (by grind only [Finset.prod_insert]))
    (add norm 0 (by grind only [Finset.erase]))
    (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodyLT'_volume]))
    (add norm 0 (by grind only [Finset.prod_eq_mul]))
    (add unsafe 90% (by rw [Finset.univ]))
    (add unsafe 90% (by rw [Finset.mem_univ]))
    (add unsafe 90% (by rw [Finset.prod_erase_mul]))
    (add unsafe 90% (by rw [Fintype.prod_eq_one]))
    (add unsafe 90% (by rw [Finset.prod_eq_single_of_mem]))
    (add unsafe 90% (by rw [Finset.subset_univ]))
    (add unsafe 90% (by rw [NumberField.InfinitePlace.mult]))
    (add unsafe 90% (by rw [Finset.prod_involution]))
    (add unsafe 90% (by rw [Fintype.prod_eq_single]))
    (add unsafe 90% (by rw [NumberField.mixedEmbedding.convexBodyLT_volume]))
    (add unsafe 90% (by rw [Finset.prod_const]))
    (add unsafe 90% (by rw [Finset.card_fin]))
    (add unsafe 90% (by rw [NumberField.InfinitePlace.sum_mult_eq]))
    (add unsafe 90% (by rw [Fintype.prod_extend_by_one]))
