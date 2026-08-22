import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators


theorem exercise_1_4 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (v : V) (a : F): a • v = 0 → a = 0 ∨ v = 0 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by omega))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [smul_eq_zero]))
    (add norm 0 (by grind only [smul_zero]))
    (add norm 0 (by grind only [zero_smul]))
    (add norm 0 (by grind only [one_smul]))
    (add norm 0 (by grind only [Algebra.Generators.Cotangent.val_smul']))
    (add norm 0 (by grind only [smul_left_injective]))
    (add norm 0 (by grind only [smul_smul]))
    (add norm 0 (by grind only [SMulCommClass]))
    (add norm 0 (by grind only [smul_assoc]))
    (add norm 0 (by grind only [LinearMap.smul_apply]))
    (add norm 0 (by grind only [map_smul]))
    (add norm 0 (by grind only [Finset.sum_smul]))
    (add norm 0 (by grind only [Algebra.Generators.Cotangent.smul_eq_zero_of_mem]))
    (add norm 0 (by grind only [Algebra.Generators.Cotangent.val_smul''']))
    (add norm 0 (by grind only [MulAction]))
    (add norm 0 (by grind only [IsLocalizedModule.eq_zero_iff]))
    (add norm 0 (by grind only [LinearPMap.map_smul]))
    (add norm 0 (by grind only [Submodule.pow_pOrder_smul]))
    (add norm 0 (by grind only [SetLike.mk_smul_mk]))
    (add norm 0 (by grind only [smul_right_injective]))
    (add norm 0 (by grind only [LinearMap.map_smulₛₗ]))
    (add norm 0 (by grind only [Algebra.Generators.Cotangent.val_smul]))
    (add norm 0 (by grind only [TrivSqZeroExt.snd_smul]))
    (add norm 0 (by grind only [Module.End.HasEigenvector.apply_eq_smul]))
    (add norm 0 (by grind only [LinearMap.map_smul]))
    (add norm 0 (by grind only [WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero]))
    (add norm 0 (by grind only [Algebra.Generators.Cotangent.val_smul'']))
    (add norm 0 (by grind only [LinearMap.map_smulₛₗ₂]))
    (add norm 0 (by grind only [MulActionWithZero]))
    (add norm 0 (by grind only [MulActionSemiHomClass]))
    (add norm 0 (by grind only [TrivSqZeroExt.inr_smul]))
    (add norm 0 (by grind only [LinearMap.BilinForm.iIsOrtho_def]))
