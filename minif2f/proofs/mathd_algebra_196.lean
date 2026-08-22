
import Mathlib

/- Vendored verbatim from google-deepmind/formal-conjectures @ f564f8d7
(Apache-2.0): the `answer()` term elaborator (FormalConjectures/Util/Answer)
and `Real.nthRoot` (FormalConjecturesForMathlib/…/NthRoot). -/

/-- Indicates where the answer is in a problem statement. -/
syntax (name := Google.answer) "answer(" term ")" : term

namespace Google
open Lean Elab Term
/-- Indicates where the answer is in a problem statement. -/
@[term_elab answer]
def answerElab : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) => do
    mkSaveInfoAnnotation <$> postponeElabTerm (← `(by exact $a)) expectedType?
  | _ => Elab.throwUnsupportedSyntax
end Google

namespace Real
/-- `nthRoot n r` computes `ⁿ√r`; behaves as expected on negatives for odd `n`. -/
noncomputable def nthRoot (n : ℕ) (r : ℝ) : ℝ :=
  if Even n then r ^ (n⁻¹ : ℝ) else SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ)
end Real

open scoped Real
open scoped Nat
open scoped Topology
open scoped Polynomial


set_option maxHeartbeats 0

theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  -- Step 1: Establish that -1 is in S
  have h1 : (-1:ℝ) ∈ S := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [mabs_of_le_one]))
      (add norm 0 (by grind only [inv_mabs_le]))
      (add norm 0 (by grind only [mabs]))
      (add norm 0 (by grind only [Set.mem_inv]))
      (add norm 0 (by grind only [inv_inv]))
      (add norm 0 (by grind only [mabs_inv]))
      (add norm 0 (by grind only [abs_eq_self]))
      (add norm 0 (by grind only [AkraBazziRecurrence.GrowsPolynomially.iff_eventuallyEq]))
      (add norm 0 (by grind only [neg_eq]))
      (add norm 0 (by grind only [mabs_of_one_le]))
      (add norm 0 (by grind only [mabs_of_lt_one]))
      (add norm 0 (by grind only [Pi.inv_apply]))
      (add norm 0 (by grind only [Rat.cast_neg]))
      (add norm 0 (by grind only [Finset.prod_inv_distrib]))
      (add norm 0 (by grind only [abs_inv]))
      (add norm 0 (by grind only [neg_inv]))
      (add norm 0 (by grind only [Finset.mem_inv]))
      (add norm 0 (by grind only [ENNReal.abs_toReal]))
      (add norm 0 (by grind only [div_neg]))
      (add norm 0 (by grind only [neg_div]))
      (add norm 0 (by grind only [Real.abs_log_sub_add_sum_range_le]))
      (add norm 0 (by grind only [HasSolidNorm]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [MeasureTheory.average_neg]))
      (add norm 0 (by grind only [norm_inv']))
      (add norm 0 (by grind only [mabs_div_comm]))
      (add norm 0 (by grind only [MeasureTheory.condexp_neg]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_iff_superpolynomialDecay_abs]))
      (add norm 0 (by grind only [inv_neg]))
      (add safe 1 (by simp_all only [div_eq_mul_inv]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))

  -- Step 2: Establish that 5 is in S
  have h2 : (5:ℝ) ∈ S := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [abs_eq_self]))
      (add norm 0 (by grind only [mabs_of_one_le]))
      (add norm 0 (by grind only [mabs_of_one_lt]))
      (add norm 0 (by grind only [one_le_mabs]))
      (add norm 0 (by grind only [mabs]))
      (add norm 0 (by grind only [abs_one]))
      (add norm 0 (by grind only [abs_pow]))
      (add norm 0 (by grind only [Nat.abs_cast]))
      (add norm 0 (by grind only [mabs_of_le_one]))
      (add norm 0 (by grind only [pow_left_strictMonoOn]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [mabs_of_lt_one]))
      (add norm 0 (by grind only [mabs_div_comm]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [abs_mul]))
      (add norm 0 (by grind only [ENNReal.abs_toReal]))
      (add norm 0 (by grind only [Real.dist_eq]))
      (add norm 0 (by grind only [mabs_inv]))
      (add norm 0 (by grind only [mabs_lt]))
      (add norm 0 (by grind only [Real.sin_bound]))
      (add norm 0 (by grind only [Real.abs_log_sub_add_sum_range_le]))
      (add norm 0 (by grind only [Real.norm_eq_abs]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [isLittleO_pow_pow_of_abs_lt_left]))
      (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq]))
      (add norm 0 (by grind only [Real.abs_rpow_of_nonneg]))
      (add norm 0 (by grind only [NNReal.abs_eq]))
      (add norm 0 (by grind only [Hyperreal.coe_abs]))
      (add norm 0 (by grind only [Int.one_le_abs]))
      (add norm 0 (by grind only [abs_inv]))
      (add norm 0 (by grind only [Real.abs_sinh]))
      (add norm 0 (by grind only [Real.abs_exp]))

  -- Step 3: Show that no other elements are in S (i.e., S contains only -1 and 5)
  have h3 : S = {-1, 5} := by
    clear * - h₀ h1 h2
    simp_rw [Finset.ext_iff, h₀]
    simp [abs_eq, sub_eq_iff_eq_add]
    exact fun x ↦
      ⟨fun Or ↦ by cases' Or with h h <;> [left; right] <;> linarith, fun Or ↦ by
        cases' Or with h h <;> [left; right] <;> linarith⟩

  -- Step 4: Calculate the sum of elements in S
  have h4 : ∑ k ∈ S, k = (-1:ℝ) + (5:ℝ) := by
    clear * - h3
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_singleton]))
      (add norm 0 (by grind only [Finset.prod_pair]))
      (add norm 0 (by grind only [Finset.mem_singleton_self]))
      (add norm 0 (by grind only [Finset.mulSpan]))
      (add norm 0 (by grind only [Finset.prod_insert]))
      (add norm 0 (by grind only [Finset.truncatedSup_singleton]))
      (add norm 0 (by grind only [Lagrange.basis_pair_left]))
      (add norm 0 (by grind only [Finset.prod_empty]))
      (add norm 0 (by grind only [Lagrange.basis_pair_right]))
      (add norm 0 (by grind only [Finset.mem_singleton]))
      (add norm 0 (by grind only [Finset.prod_const_one]))
      (add norm 0 (by grind only [Lagrange.interpolate_eq_add_interpolate_erase]))
      (add norm 0 (by grind only [Finset.fold_insert]))
      (add norm 0 (by grind only [Finset.filter_singleton]))
      (add norm 0 (by grind only [Lagrange.basis_singleton]))
      (add norm 0 (by grind only [Finset.image_insert]))
      (add norm 0 (by grind only [Nat.binomial_eq_choose]))
      (add norm 0 (by grind only [Finset.gcd_singleton]))
      (add norm 0 (by grind only [Finset.not_mem_singleton]))
      (add norm 0 (by grind only [Set.finset_prod_singleton]))
      (add norm 0 (by grind only [Finset.sup_singleton]))
      (add norm 0 (by grind only [Finset.single_le_prod']))
      (add norm 0 (by grind only [Finset.biUnion_insert]))
      (add norm 0 (by grind only [AhlswedeZhang.supSum_singleton]))
      (add norm 0 (by grind only [Finset.prod_apply]))
      (add norm 0 (by grind only [Finset.gcd_insert]))
      (add norm 0 (by grind only [Finset.mem_insert]))
      (add norm 0 (by grind only [Finset.prod_insert_one]))
      (add norm 0 (by grind only [Lagrange.interpolate_one]))
      (add norm 0 (by grind only [Lagrange.interpolate_eq_sum_interpolate_insert_sdiff]))
      (add norm 0 (by grind only [Finset.eq_singleton_iff_unique_mem]))
      (add norm 0 (by grind only [Nat.insert_self_properDivisors]))

  -- Step 5: Simplify the sum
  have h5 : (-1:ℝ) + (5:ℝ) = 4 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 1 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by rw [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self']))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [Real.arctan_inv_2_add_arctan_inv_3]))
      (add norm 0 (by grind only [Real.two_mul_arctan_inv_3_add_arctan_inv_7]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star']))
      (add norm 0 (by rw [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [parallelogram_law]))
      (add norm 0 (by rw [jacobiTheta_two_add]))
      (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
      (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
      (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add norm 0 (by rw [div_inv_eq_mul]))
      (add norm 0 (by grind only [Ring.multichoose_two]))
      (add norm 0 (by grind only [Real.two_mul_arctan_inv_2_sub_arctan_inv_7]))
      (add norm 0 (by grind only [Finset.mulETransformRight.card]))
      (add norm 0 (by grind only [Complex.sin_two_mul]))
      (add norm 0 (by rw [gold_add_goldConj]))
      (add norm 0 (by grind only [Nat.fib_two_mul]))
      (add unsafe 50% (by nlinarith [Real.arctan_add_eq_sub_pi]))

  -- Step 6: Conclude the proof
  have h6 : ∑ k ∈ S, k = 4 := by
    clear * - h4 h5
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [inv_eq_iff_eq_inv]))
      (add norm 0 (by grind only [neg_eq]))
      (add norm 0 (by grind only [inv_inj]))
      (add norm 0 (by grind only [InvMemClass.coe_inv]))
      (add norm 0 (by grind only [neg_mul]))
      (add norm 0 (by grind only [inv_inv]))
      (add norm 0 (by grind only [neg_lie]))
      (add norm 0 (by grind only [neg_inv]))
      (add norm 0 (by grind only [Finset.prod_inv_distrib]))
      (add norm 0 (by grind only [inv_eq_one]))
      (add norm 0 (by grind only [inv_neg]))
      (add norm 0 (by grind only [Quaternion.star_eq_neg]))
      (add norm 0 (by grind only [FormalMultilinearSeries.neg_apply]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [neg_one_smul]))
      (add norm 0 (by grind only [LieModule.chainTop_neg]))
      (add unsafe 50% (by nlinarith [mul_eq_one_iff_eq_inv]))
      (add unsafe 50% (by nlinarith [inv_eq_iff_mul_eq_one]))
      (add unsafe 50% (by nlinarith [eq_inv_iff_mul_eq_one]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [neg_one_mul]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [mul_eq_one_iff_inv_eq]))
      (add unsafe 50% (by nlinarith [IsGroupHom.one_iff_ker_inv]))
      (add unsafe 50% (by nlinarith [mul_right_inv]))
      (add unsafe 50% (by nlinarith [neg_eq_neg_one_mul]))
      (add unsafe 50% (by nlinarith [mul_neg_one]))
      (add unsafe 50% (by nlinarith [neg_mul_neg]))
      (add unsafe 50% (by nlinarith [QuaternionAlgebra.star_eq_neg]))
      (add unsafe 50% (by nlinarith [inv_mul_eq_one]))

  exact h6
