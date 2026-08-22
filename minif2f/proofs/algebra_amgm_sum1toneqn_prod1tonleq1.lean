
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

theorem algebra_amgm_sum1toneqn_prod1tonleq1 (a : ℕ → NNReal) (n : ℕ)
    (h₀ : ∑ x ∈ Finset.range n, a x = n) : ∏ x ∈ Finset.range n, a x ≤ 1 := by
  -- Step 1: For all x < n, a_x <= exp(a_x - 1)
  have h1 : ∀ x ∈ Finset.range n, (a x : ℝ) ≤ Real.exp ((a x : ℝ) - 1) := by
    clear * -
    intro x _
    linarith [Real.add_one_le_exp (a x - (1 : ℝ))]

  -- Step 2: Product of a_x <= Product of exp(a_x - 1)
  have h2 : ∏ x ∈ Finset.range n, (a x : ℝ) ≤ ∏ x ∈ Finset.range n, Real.exp ((a x : ℝ) - 1) := by
    clear * - h1
    refine' Finset.prod_le_prod _ _
    · exact fun x hx ↦ NNReal.coe_nonneg _
    · exact_mod_cast h1

  -- Step 3: Product of exp(a_x - 1) = exp(Sum(a_x - 1))
  have h3 : ∏ x ∈ Finset.range n, Real.exp ((a x : ℝ) - 1) = Real.exp (∑ x ∈ Finset.range n, ((a x : ℝ) - 1)) := by
    clear * -
    rw [← Real.exp_sum]

  -- Step 4: Sum(a_x - 1) = Sum(a_x) - Sum(1)
  have h4 : ∑ x ∈ Finset.range n, ((a x : ℝ) - 1) = (∑ x ∈ Finset.range n, (a x : ℝ)) - ∑ x ∈ Finset.range n, (1 : ℝ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by simp))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_congr]))
      (add norm 0 (by grind only [Finset.prod_subset]))
      (add norm 0 (by grind only [rfl]))
      (add norm 0 (by grind only [Finset.sum_mul]))
      (add norm 0 (by grind only [Finset.prod_comm]))
      (add norm 0 (by grind only [ClassGroup.cardM]))
      (add norm 0 (by grind only [BoxIntegral.BoxAdditiveMap.sum_boxes_congr]))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add norm 0 (by grind only [BoxIntegral.Prepartition.sum_biUnion_boxes]))
      (add norm 0 (by grind only [Finset.prod_div_distrib]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Finset.prod_sigma']))
      (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
      (add norm 0 (by grind only [MvPolynomial.NewtonIdentities.esymm_mul_psum_summand_to_weight]))
      (add norm 0 (by grind only [SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint]))
      (add norm 0 (by grind only [MvPolynomial.NewtonIdentities.esymm_mul_psum_to_weight]))
      (add norm 0 (by grind only [Finset.prod_range_div_prod_range]))
      (add norm 0 (by grind only [Finset.sum_range_reflect]))
      (add norm 0 (by grind only [Finset.prod_Ico_eq_div]))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [MvPowerSeries.mul_invOfUnit]))
      (add norm 0 (by grind only [Fintype.prod_congr]))
      (add norm 0 (by grind only [Finset.prod_le_prod']))
      (add norm 0 (by grind only [Finset.prod_attach]))
      (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
      (add norm 0 (by grind only [binomial_sum_eq]))
      (add norm 0 (by grind only [BoxIntegral.BoxAdditiveMap.sum_partition_boxes]))
      (add norm 0 (by grind only [Finset.prod_range_div]))
      (add norm 0 (by grind only [numDerangements_sum]))
      (add norm 0 (by grind only [MeasureTheory.SignedMeasure.measureOfNegatives]))
      (add norm 0 (by grind only [MvPolynomial.NewtonIdentities.esymm_summand_to_weight]))

  -- Step 5: Sum_{x=0}^{n-1} 1 = n
  have h5 : ∑ x ∈ Finset.range n, (1 : ℝ) = (n : ℝ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by ring_nf at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.choose_self]))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [Finset.range_succ]))
      (add norm 0 (by grind only [Nat.choose_succ_self_right]))
      (add norm 0 (by grind only [Nat.choose_zero_right]))
      (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
      (add norm 0 (by grind only [bernsteinPolynomial.sum]))
      (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
      (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
      (add norm 0 (by grind only [numDerangements_sum]))
      (add norm 0 (by grind only [Finset.prod_range_one]))
      (add norm 0 (by grind only [bernsteinPolynomial.sum_smul]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [Finset.prod_range_zero]))
      (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [Nat.choose_one_right]))
      (add norm 0 (by grind only [Finset.range_add_one]))
      (add norm 0 (by grind only [Nat.factorial]))
      (add norm 0 (by grind only [numDerangements]))
      (add norm 0 (by grind only [add_pow]))
      (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
      (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk]))
      (add norm 0 (by grind only [Nat.cast_sum]))
      (add safe 0 (by simp only [Finset.range_one] at *))
      (add unsafe 90% (by norm_num [Nat.prod_range_factorial_succ] at *))

  -- Step 6: Sum(a_x) = n (from hypothesis h0, casting to real)
  have h6 : ∑ x ∈ Finset.range n, (a x : ℝ) = (n : ℝ) := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.cast_sum]))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [numDerangements_sum]))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [Rat.cast_sum]))
      (add norm 0 (by grind only [NNReal.coe_sum]))
      (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
      (add norm 0 (by grind only [Nat.cast_prod]))
      (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
      (add norm 0 (by grind only [NNReal.coe_prod]))
      (add norm 0 (by grind only [binomial_sum_eq]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [sum_range_pow]))
      (add norm 0 (by grind only [Finset.sum_range_id]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
      (add norm 0 (by grind only [Finset.sum_range_reflect]))
      (add norm 0 (by grind only [bernsteinPolynomial.sum_smul]))
      (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [Finset.prod_le_prod']))
      (add norm 0 (by grind only [Finset.prod_const]))
      (add norm 0 (by grind only [ENNReal.coe_finset_sum]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
      (add norm 0 (by grind only [Finset.prod_range_div_prod_range]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [Finset.prod_range_div]))
      (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
      (add norm 0 (by grind only [Finset.sum_mul]))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add safe 1 (by simp_all only [Finset.prod_natCast]))

  -- Step 7: Combine h4, h6, h5 to get Sum(a_x - 1) = n - n = 0
  have h7 : ∑ x ∈ Finset.range n, ((a x : ℝ) - 1) = (0 : ℝ) := by
    clear * - h4 h6 h5
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [Finset.prod_eq_one]))
      (add norm 0 (by grind only [Finset.prod_eq_zero]))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add norm 0 (by grind only [Nat.cast_sum]))
      (add norm 0 (by grind only [Finset.single_le_prod']))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
      (add norm 0 (by grind only [Finset.prod_eq_one_iff']))
      (add norm 0 (by grind only [geom_sum_mul]))
      (add norm 0 (by grind only [Finset.prod_le_prod']))
      (add norm 0 (by grind only [Finset.prod_const_one]))
      (add norm 0 (by grind only [mul_geom_sum]))
      (add norm 0 (by grind only [Finset.sum_mul]))
      (add norm 0 (by grind only [geom_sum_mul_neg]))
      (add norm 0 (by grind only [Finset.prod_Ico_eq_div]))
      (add norm 0 (by grind only [MeasureTheory.mul_upcrossingsBefore_le]))
      (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
      (add norm 0 (by grind only [MeasureTheory.BorelCantelli.predictablePart_process_ae_eq]))
      (add norm 0 (by grind only [Finset.prod_range_div]))
      (add norm 0 (by grind only [numDerangements_sum]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [Finset.prod_range_mul_prod_Ico]))
      (add norm 0 (by grind only [binomial_sum_eq]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add unsafe 90% (by rw [Finset.prod_div_distrib]))
      (add unsafe 90% (by rw [Finset.prod]))
      (add unsafe 90% (by rw [Finset.prod_apply]))
      (add unsafe 90% (by rw [Finset.prod_const]))
      (add unsafe 90% (by rw [Finset.prod_attach]))

  -- Step 8: exp(0) = 1
  have h8 : Real.exp (0 : ℝ) = (1 : ℝ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add norm 0 (by decide))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.exp_zero]))
      (add norm 0 (by grind only [Real.log_exp]))
      (add norm 0 (by grind only [Real.exp_arsinh]))
      (add norm 0 (by grind only [integral_exp]))
      (add norm 0 (by grind only [Real.exp]))
      (add norm 0 (by grind only [Real.exp_eq_exp_ℝ]))
      (add norm 0 (by grind only [Real.exp_log]))
      (add norm 0 (by grind only [Real.exp_mul]))
      (add norm 0 (by grind only [Real.exp_ne_zero]))
      (add norm 0 (by grind only [NormedSpace.of_real_exp_ℝ_ℝ]))
      (add norm 0 (by grind only [Real.exp_add]))
      (add norm 0 (by grind only [rexp_neg_injOn_aux]))
      (add norm 0 (by grind only [Real.exp_sub]))
      (add norm 0 (by grind only [Real.exp_eq_exp]))
      (add norm 0 (by grind only [Real.exp_pos]))
      (add norm 0 (by grind only [rexp_neg_deriv_aux]))
      (add norm 0 (by grind only [Real.exp_one_rpow]))
      (add norm 0 (by grind only [Real.exp_nat_mul]))
      (add norm 0 (by grind only [Real.exp_log_eq_abs]))
      (add norm 0 (by grind only [Real.exp_injective]))
      (add norm 0 (by grind only [Real.exp_half]))
      (add norm 0 (by grind only [Complex.ofReal_exp]))
      (add norm 0 (by grind only [rexp_neg_image_aux]))
      (add norm 0 (by grind only [Real.exp_le_exp]))
      (add norm 0 (by grind only [Complex.exp_eq_exp_ℂ]))
      (add norm 0 (by grind only [Real.rpow_def_of_pos]))
      (add norm 0 (by grind only [ProbabilityTheory.mgf]))
      (add norm 0 (by grind only [Real.measurable_exp]))
      (add norm 0 (by grind only [NormedSpace.exp_ℝ_ℂ_eq_exp_ℂ_ℂ]))
      (add norm 0 (by rw [Quaternion.exp_coe]))
      (add norm 0 (by grind only [Real.exp_eq_one_iff]))
      (add norm 0 (by grind only [Real.exp_nonneg]))

  -- Step 9: Therefore, Product of exp(...) = 1
  have h9 : ∏ x ∈ Finset.range n, Real.exp ((a x : ℝ) - 1) = (1 : ℝ) := by
    clear * - h3 h7 h8
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.exp_sum]))
      (add norm 0 (by grind only [Finset.prod_const_one]))
      (add norm 0 (by grind only [Finset.prod_eq_zero]))
      (add norm 0 (by grind only [Finset.prod_eq_one]))
      (add norm 0 (by grind only [Finset.prod_eq_one_iff']))
      (add norm 0 (by grind only [Complex.exp_sum]))
      (add norm 0 (by grind only [Finset.single_le_prod']))
      (add norm 0 (by grind only [Finset.prod_singleton]))
      (add norm 0 (by grind only [Finset.prod_eq_one_iff_of_one_le']))
      (add norm 0 (by grind only [Finset.prod_eq_single]))
      (add norm 0 (by grind only [Finset.prod_empty]))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Finset.prod_subset]))
      (add norm 0 (by grind only [MeasureTheory.BorelCantelli.process]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [FiniteField.sum_pow_units]))
      (add norm 0 (by grind only [MeasureTheory.BorelCantelli.predictablePart_process_ae_eq]))
      (add norm 0 (by grind only [Real.log_prod]))
      (add norm 0 (by grind only [MeasureTheory.BorelCantelli.martingalePart_process_ae_eq]))
      (add norm 0 (by grind only [Finset.prod_congr]))
      (add norm 0 (by grind only [Lagrange.interpolate]))
      (add norm 0 (by grind only [MeasureTheory.integrable_finset_sum']))
      (add norm 0 (by grind only [Finset.prod_insert]))
      (add norm 0 (by grind only [FiniteField.sum_pow_lt_card_sub_one]))
      (add norm 0 (by grind only [Real.exp_zero]))
      (add unsafe 90% (by rw [Finset.prod_apply]))
      (add unsafe 90% (by rw [Finset.prod_div_distrib]))
      (add unsafe 90% (by rw [Finset.prod_eq_single_of_mem]))
      (add unsafe 90% (by rw [Finset.prod]))
      (add unsafe 90% (by rw [Fintype.prod_eq_one]))
      (add unsafe 90% (by rw [Finset.prod_attach]))

  -- Step 10: Final conclusion
  have h10 : ∏ x ∈ Finset.range n, (a x : ℝ) ≤ (1 : ℝ) := by
    clear * - h2 h9
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
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
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 0 (by push_neg))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.range_mono]))
      (add norm 0 (by grind only [Finset.prod_le_prod']))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [Finset.sum_schlomilch_le']))
      (add norm 0 (by grind only [Finset.single_le_prod']))
      (add norm 0 (by grind only [le_mul_iff_one_le_left']))
      (add norm 0 (by grind only [le_mul_iff_one_le_right']))
      (add norm 0 (by grind only [zero_le']))
      (add norm 0 (by grind only [eVariationOn.sum_le]))
      (add norm 0 (by grind only [Finset.Ico]))
      (add norm 0 (by grind only [le_rfl]))
      (add norm 0 (by grind only [Finset.prod_le_prod_of_subset_of_one_le']))
      (add norm 0 (by grind only [Finset.range_eq_Ico]))
      (add norm 0 (by grind only [Finset.le_sum_schlomilch']))
      (add norm 0 (by grind only [MeasureTheory.mul_upcrossingsBefore_le]))
      (add norm 0 (by grind only [Finset.prod_range_mul_prod_Ico]))
      (add norm 0 (by grind only [Finset.Ico_subset_Ico]))
      (add norm 0 (by grind only [Finset.sum_schlomilch_le]))
      (add norm 0 (by grind only [le_refl]))
      (add norm 0 (by grind only [Finset.one_le_prod']))
      (add norm 0 (by grind only [Finset.prod_le_prod]))
      (add norm 0 (by grind only [Finset.prod_le_one']))
      (add norm 0 (by grind only [NNReal.coe_mono]))
      (add norm 0 (by grind only [prod_le_tprod]))
      (add norm 0 (by grind only [Finset.range_subset]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodySumFun_nonneg]))
      (add norm 0 (by grind only [Finset.mem_range_le]))
      (add norm 0 (by grind only [Finset.prod_nonneg]))
      (add norm 0 (by grind only [Nat.mono_cast]))
      (add unsafe 10% (by grind only [one_le]))
      (add unsafe 10% (by grind only [le_trans]))
      (add unsafe 10% (by grind only [Finset.mem_range_succ_iff]))

  -- Cast back to NNReal context if necessary, but the target is already real comparison or NNReal comparison
  -- The goal is ∏ ... ≤ 1. Since a maps to NNReal, the product is an NNReal.
  -- We proved the real version. We need to lift the inequality.
  -- Actually, the statement uses NNReal. The coercion to Real is monotone.
  -- Let's ensure the final step matches the type system expectations.
  -- The goal is `∏ x ∈ Finset.range n, a x ≤ 1`.
  -- `h10` proves `(↑(∏ x ∈ Finset.range n, a x) : ℝ) ≤ 1`.
  -- This implies the inequality in NNReal because the coercion is order-preserving and injective.

  exact_mod_cast h10
