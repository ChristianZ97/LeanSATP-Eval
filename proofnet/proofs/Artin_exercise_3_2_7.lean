import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd RingHom
open scoped BigOperators


theorem exercise_3_2_7 {F : Type*} [Field F] {G : Type*} [Field G]
  (φ : F →+* G) : Injective φ := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 1 (by ring_nf at *))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [RingHom.injective]))
    (add norm 0 (by grind only [injective_iff_map_eq_one]))
    (add norm 0 (by grind only [RingHom.injective_int]))
    (add norm 0 (by grind only [Function.Injective.comp]))
    (add norm 0 (by grind only [exists_isTranscendenceBasis]))
    (add norm 0 (by grind only [Function.Injective.of_comp]))
    (add norm 0 (by grind only [IsScalarTower.algebraMap_eq]))
    (add norm 0 (by grind only [algebraMap]))
    (add norm 0 (by grind only [IsFractionRing.injective]))
    (add norm 0 (by grind only [exists_integral_multiple]))
    (add norm 0 (by grind only [IsIntegralClosure.algebraMap_injective]))
    (add norm 0 (by grind only [injective_iff_map_eq_one']))
    (add norm 0 (by grind only [NoZeroSMulDivisors.algebraMap_injective]))
    (add norm 0 (by grind only [isIntegral_algebraMap_iff]))
    (add norm 0 (by grind only [Function.Injective]))
    (add norm 0 (by grind only [Polynomial.map_injective]))
    (add norm 0 (by grind only [map_ne_one_iff]))
    (add norm 0 (by grind only [algebraMap_injective]))
    (add norm 0 (by grind only [IsIntegralClosure.exists_smul_eq_mul]))
    (add norm 0 (by grind only [Function.Injective.eq_iff]))
    (add norm 0 (by grind only [isIntegrallyClosed_iff]))
    (add norm 0 (by grind only [map_eq_one_iff]))
    (add norm 0 (by grind only [AlgHomClass.unitization_injective']))
    (add norm 0 (by grind only [Polynomial.SplittingField.splits]))
    (add norm 0 (by grind only [IsIntegrallyClosed.isIntegral_iff]))
    (add norm 0 (by grind only [AlgHomClass.unitization_injective]))
    (add norm 0 (by grind only [IsIntegrallyClosed.algebraMap_eq_of_integral]))
    (add norm 0 (by grind only [Polynomial.IsSplittingField.splits]))
    (add norm 0 (by grind only [mem_nonZeroDivisors_iff_ne_zero]))
    (add norm 0 (by grind only [isIntegral_algebraMap]))
    (add norm 0 (by grind only [IsPrimitiveRoot.map_iff_of_injective]))
    (add norm 0 (by grind only [ClassGroup.exists_mem_finset_approx']))
