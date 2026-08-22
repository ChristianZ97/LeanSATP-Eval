
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

theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    ∑ k ∈ S, k = -6 := by
  -- Step 1: Define the two potential solutions based on (x+3)^2 = 121 implies x+3 = 11 or x+3 = -11
  have h₁ : (-14 : ℝ) ∈ S := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [Polynomial.cyclotomic_two]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [sq_eq_sq_iff_eq_or_eq_neg]))
      (add norm 0 (by grind only [Derivation.leibniz_of_mul_eq_one]))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [IsSquare_sq]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [Quaternion.sq_eq_neg_normSq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [IsCyclotomicExtension.Rat.Three.lambda_sq]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [ENNReal.rpow_two]))
      (add norm 0 (by grind only [CoxeterSystem.IsReflection.pow_two]))
      (add norm 0 (by grind only [IsPrimitiveRoot.eq_neg_one_of_two_right]))
      (add norm 0 (by grind only [Quaternion.star_eq_neg]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [inv_mem_iff]))
      (add norm 0 (by grind only [IsPrimitiveRoot.neg_one]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by nlinarith [mul_eq_one_iff_eq_inv]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by nlinarith [inv_eq_iff_mul_eq_one]))
      (add unsafe 50% (by nlinarith [eq_inv_iff_mul_eq_one]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))

  have h₂ : (8 : ℝ) ∈ S := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [IsSquare_sq]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [CoxeterSystem.IsReflection.pow_two]))
      (add norm 0 (by grind only [Polynomial.cyclotomic_two]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [CharTwo.sum_sq]))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [ENNReal.rpow_two] at *))
      (add unsafe 90% (by simp only [Complex.cpow_two] at *))
      (add unsafe 90% (by simp only [NNReal.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))

  -- Step 2: Prove that these are the only elements in S
  have h₃ : S = ({-14, 8} : Finset ℝ) := by
    clear * - h₀ h₁ h₂
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
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.truncatedSup_singleton]))
      (add norm 0 (by grind only [Finset.mem_singleton_self]))
      (add norm 0 (by grind only [Lagrange.basis_pair_right]))
      (add norm 0 (by grind only [Lagrange.basis_pair_left]))
      (add norm 0 (by grind only [Finset.coe_singleton]))
      (add norm 0 (by grind only [Finset.eq_singleton_iff_unique_mem]))
      (add norm 0 (by grind only [Finset.prod_pair]))
      (add norm 0 (by grind only [Finset.mulSpan]))
      (add norm 0 (by grind only [Finset.mem_singleton]))
      (add norm 0 (by grind only [Finset.not_mem_singleton]))
      (add norm 0 (by grind only [subset_antisymm]))
      (add norm 0 (by grind only [Nat.binomial_eq_choose]))
      (add norm 0 (by grind only [Set.equitableOn_singleton]))
      (add norm 0 (by grind only [Finset.truncatedInf_singleton]))
      (add norm 0 (by grind only [SimpleGraph.TripartiteFromTriangles.graph_triple]))
      (add norm 0 (by grind only [Finset.card_pair]))
      (add norm 0 (by grind only [Finset.set_biInter_singleton]))
      (add norm 0 (by grind only [Set.ncard_pair]))
      (add norm 0 (by grind only [SimpleGraph.triple_eq_triple_of_mem]))
      (add norm 0 (by grind only [Eq.symm]))
      (add norm 0 (by grind only [Finset.image_singleton]))
      (add norm 0 (by grind only [Set.pairwise_singleton]))
      (add norm 0 (by grind only [Finset.pair_comm]))
      (add norm 0 (by grind only [Nat.binomial_eq]))
      (add norm 0 (by grind only [Multiset.card_pair]))
      (add norm 0 (by grind only [Finset.coe_eq_singleton]))
      (add norm 0 (by grind only [Lagrange.basis_singleton]))
      (add norm 0 (by grind only [Finset.card_singleton]))
      (add norm 0 (by grind only [Set.pairwiseDisjoint_singleton]))
      (add norm 0 (by grind only [Set.image_singleton]))
      (add norm 0 (by grind only [Set.singleton_def]))
      (add norm 0 (by grind only [IsLocalizedModule.finsetIntegerMultiple_image]))

  -- Step 3: Calculate the sum of elements in S
  have h₄ : ∑ k ∈ S, k = ∑ k ∈ ({-14, 8} : Finset ℝ), k := by
    clear * - h₃
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
      (add norm 0 (by ring_nf))
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
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_pair]))
      (add norm 0 (by grind only [Finset.prod_singleton]))
      (add norm 0 (by grind only [Finset.mem_singleton_self]))
      (add norm 0 (by grind only [Finset.mulSpan]))
      (add norm 0 (by grind only [Lagrange.basis_pair_left]))
      (add norm 0 (by grind only [Lagrange.basis_pair_right]))
      (add norm 0 (by grind only [Finset.truncatedSup_singleton]))
      (add norm 0 (by grind only [Finset.mem_singleton]))
      (add norm 0 (by grind only [Finset.prod_insert]))
      (add norm 0 (by grind only [Finset.not_mem_singleton]))
      (add norm 0 (by grind only [Nat.binomial_eq_choose]))
      (add norm 0 (by grind only [Finset.fold_insert]))
      (add norm 0 (by grind only [Lagrange.basis_singleton]))
      (add norm 0 (by grind only [Finset.filter_singleton]))
      (add norm 0 (by grind only [Lagrange.interpolate_eq_add_interpolate_erase]))
      (add norm 0 (by grind only [Finset.image_insert]))
      (add norm 0 (by grind only [Finset.gcd_singleton]))
      (add norm 0 (by grind only [Finset.mem_insert]))
      (add norm 0 (by grind only [Set.finset_prod_singleton]))
      (add norm 0 (by grind only [Finset.set_biInter_singleton]))
      (add norm 0 (by grind only [Finset.biUnion_insert]))
      (add norm 0 (by grind only [Finset.prod_empty]))
      (add norm 0 (by grind only [Finset.insert_eq]))
      (add norm 0 (by grind only [Nat.binomial_eq]))
      (add norm 0 (by grind only [Finset.pair_comm]))
      (add norm 0 (by grind only [Finset.eq_singleton_iff_unique_mem]))
      (add norm 0 (by grind only [Finset.gcd_insert]))
      (add norm 0 (by grind only [Finset.mem_insert_self]))
      (add norm 0 (by grind only [Finset.sup_singleton]))
      (add norm 0 (by grind only [Finset.weightedVSubOfPoint_insert]))
      (add norm 0 (by grind only [Finset.prod_const_one]))
      (add norm 0 (by grind only [Finset.mem_insert_of_mem]))

  -- Step 4: Compute the explicit sum
  have h₅ : ∑ k ∈ ({-14, 8} : Finset ℝ), k = (-14 : ℝ) + (8 : ℝ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by rfl))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_singleton]))
      (add norm 0 (by grind only [Finset.prod_pair]))
      (add norm 0 (by grind only [Lagrange.basis_pair_left]))
      (add norm 0 (by grind only [Lagrange.basis_pair_right]))
      (add norm 0 (by grind only [Finset.mulSpan]))
      (add norm 0 (by grind only [Finset.prod_insert]))
      (add norm 0 (by grind only [Finset.prod_empty]))
      (add norm 0 (by grind only [Nat.binomial_eq_choose]))
      (add norm 0 (by grind only [Finset.mem_singleton_self]))
      (add norm 0 (by grind only [Lagrange.interpolate_eq_add_interpolate_erase]))
      (add norm 0 (by grind only [Finset.mem_singleton]))
      (add norm 0 (by grind only [Finset.truncatedSup_singleton]))
      (add norm 0 (by grind only [Finset.fold_insert]))
      (add norm 0 (by grind only [Finset.gcd_singleton]))
      (add norm 0 (by grind only [Nat.binomial_eq]))
      (add norm 0 (by grind only [Lagrange.basis_singleton]))
      (add norm 0 (by grind only [Finset.not_mem_singleton]))
      (add norm 0 (by grind only [Finset.gcd_insert]))
      (add norm 0 (by grind only [Finset.prod_const_one]))
      (add norm 0 (by grind only [Finset.filter_singleton]))
      (add norm 0 (by grind only [Finset.image_insert]))
      (add norm 0 (by grind only [Nat.insert_self_properDivisors]))
      (add norm 0 (by grind only [Finset.pair_comm]))
      (add norm 0 (by grind only [Finset.insert_eq]))
      (add norm 0 (by grind only [Finset.prod_insert_one]))
      (add norm 0 (by grind only [Finset.map_insert]))
      (add norm 0 (by grind only [Lagrange.interpolate_one]))
      (add norm 0 (by grind only [Finset.range_one]))
      (add norm 0 (by grind only [Finset.set_biInter_singleton]))
      (add norm 0 (by grind only [Finset.mem_insert]))
      (add norm 0 (by grind only [Set.finset_prod_singleton]))
      (add norm 0 (by grind only [Finset.insert_eq_of_mem]))

  -- Step 5: Final arithmetic
  have h₆ : (-14 : ℝ) + (8 : ℝ) = (-6 : ℝ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [neg_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
      (add norm 0 (by grind only [Quaternion.mul_imI]))
      (add norm 0 (by grind only [QuaternionAlgebra.Basis]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [neg_one_smul]))
      (add norm 0 (by grind only [QuaternionAlgebra.Basis.k_mul_i]))
      (add norm 0 (by grind only [neg_eq]))
      (add unsafe 50% (by nlinarith [mul_neg_one]))
      (add unsafe 50% (by nlinarith [neg_one_mul]))
      (add unsafe 50% (by nlinarith [Complex.I_mul_I]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imJ]))
      (add unsafe 50% (by nlinarith [Complex.inv_I]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imJ]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [neg_mul_neg]))
      (add unsafe 50% (by nlinarith [Complex.I_sq]))
      (add unsafe 50% (by nlinarith [neg_mul_eq_neg_mul]))
      (add unsafe 50% (by nlinarith [neg_eq_neg_one_mul]))
      (add unsafe 50% (by nlinarith [neg_mul_comm]))
      (add unsafe 50% (by nlinarith [Quaternion.mul_imJ]))
      (add unsafe 50% (by nlinarith [QuaternionAlgebra.neg_imJ]))
      (add unsafe 50% (by nlinarith [QuaternionAlgebra.neg_imI]))
      (add unsafe 50% (by nlinarith [mul_left_inv]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imI]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imI]))
      (add unsafe 50% (by nlinarith [Complex.div_I]))
      (add unsafe 50% (by nlinarith [neg_npow_assoc]))
      (add unsafe 50% (by nlinarith [neg_div]))
      (add unsafe 50% (by nlinarith [HurwitzZeta.jacobiTheta₂''_neg_left]))
      (add unsafe 50% (by nlinarith [WeierstrassCurve.ψ_neg]))

  -- Conclusion
  have h₇ : ∑ k ∈ S, k = (-6 : ℝ) := by
    clear * - h₄ h₅ h₆
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_pair]))
      (add norm 0 (by grind only [Finset.mem_singleton_self]))
      (add norm 0 (by grind only [Finset.prod_singleton]))
      (add norm 0 (by grind only [Finset.mem_singleton]))
      (add norm 0 (by grind only [Lagrange.basis_pair_left]))
      (add norm 0 (by grind only [Finset.prod_insert]))
      (add norm 0 (by grind only [Finset.mulSpan]))
      (add norm 0 (by grind only [Lagrange.basis_pair_right]))
      (add norm 0 (by grind only [Lagrange.interpolate_eq_add_interpolate_erase]))
      (add norm 0 (by grind only [Finset.mem_insert]))
      (add norm 0 (by grind only [Finset.fold_insert]))
      (add norm 0 (by grind only [Finset.mem_insert_self]))
      (add norm 0 (by grind only [Nat.binomial_eq_choose]))
      (add norm 0 (by grind only [Finset.mem_insert_of_mem]))
      (add norm 0 (by grind only [Finset.not_mem_singleton]))
      (add norm 0 (by grind only [Finset.truncatedSup_singleton]))
      (add norm 0 (by grind only [mul_not_mem_of_exponent_two]))
      (add norm 0 (by grind only [Finset.biUnion_insert]))
      (add norm 0 (by grind only [Finset.prod_insert_one]))
      (add norm 0 (by grind only [Finset.insert_eq_of_mem]))
      (add norm 0 (by grind only [Finset.image_insert]))
      (add norm 0 (by grind only [Finset.weightedVSubOfPoint_insert]))
      (add norm 0 (by grind only [Finset.prod_empty]))
      (add norm 0 (by grind only [Finset.gcd_insert]))
      (add norm 0 (by grind only [Finset.sup_insert]))
      (add norm 0 (by grind only [Finset.insert_eq]))
      (add norm 0 (by grind only [Lagrange.interpolate_eq_sum_interpolate_insert_sdiff]))
      (add norm 0 (by grind only [Finset.card_pair]))
      (add norm 0 (by grind only [Finset.prod_const_one]))
      (add norm 0 (by grind only [Finset.gcd_singleton]))
      (add norm 0 (by grind only [Nat.binomial_eq]))
      (add norm 0 (by grind only [Turing.TM1.stmts₁]))

  exact h₇
