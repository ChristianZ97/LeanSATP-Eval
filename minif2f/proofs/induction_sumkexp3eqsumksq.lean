
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

theorem induction_sumkexp3eqsumksq (n : ℕ) :
    ∑ k ∈ Finset.range n, k ^ 3 = (∑ k ∈ Finset.range n, k) ^ 2 := by
  -- We prove this by induction on n.
  induction n with
  | zero =>
    -- Base case: n = 0
    -- Step 1 & 2 informal proof corresponds to base case logic, though ranges are empty.
    have h_base : ∑ k ∈ Finset.range 0, k ^ 3 = 0 := by
      clear * -
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 380
        maxNormIterations := 320
        enableSimp := false
        enableUnfold := false
        })
        (add norm 0 (by ring))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by positivity))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 100 (by ring_nf))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by ext))
        (add safe 0 (by split))
        (add safe 0 (by exfalso))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Finset.prod_range_zero]))
        (add norm 0 (by grind only [Finset.range_zero]))
        (add norm 0 (by grind only [Finset.prod_range_one]))
        (add norm 0 (by grind only [Nat.choose_zero_right]))
        (add norm 0 (by grind only [Nat.choose_self]))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [Nat.factorial_zero]))
        (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
        (add norm 0 (by grind only [Finset.prod_empty]))
        (add norm 0 (by grind only [pow_zero]))
        (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
        (add norm 0 (by grind only [sum_bernoulli]))
        (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
        (add norm 0 (by grind only [tsub_zero]))
        (add norm 0 (by grind only [ArithmeticFunction.vonMangoldt_apply_one]))
        (add norm 0 (by grind only [tsub_self]))
        (add norm 0 (by grind only [Nat.choose_succ_self]))
        (add norm 0 (by grind only [bernsteinPolynomial.sum]))
        (add norm 0 (by grind only [Finset.prod_singleton]))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [numDerangements]))
        (add norm 0 (by grind only [Nat.zero_eq]))
        (add norm 0 (by grind only [Nat.Ico_zero_eq_range]))
        (add norm 0 (by grind only [Polynomial.hermite_zero]))
        (add norm 0 (by grind only [Finset.range_succ]))
        (add norm 0 (by grind only [MvPolynomial.esymm_zero]))
        (add norm 0 (by grind only [Finset.range_add_one]))
        (add norm 0 (by grind only [Nat.centralBinom_zero]))
        (add norm 0 (by grind only [Finset.card_range]))
        (add safe 0 (by simp only [Finset.range_one] at *))
        (add safe 0 (by simp only [bernoulli_zero] at *))

    have h_base_sq : (∑ k ∈ Finset.range 0, k) ^ 2 = 0 := by
      clear * -
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 380
        maxNormIterations := 320
        enableSimp := false
        enableUnfold := false
        })
        (add norm 0 (by ring))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by positivity))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 100 (by ring_nf))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by ext))
        (add safe 0 (by split))
        (add safe 0 (by exfalso))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Finset.prod_range_zero]))
        (add norm 0 (by grind only [Finset.range_zero]))
        (add norm 0 (by grind only [Finset.prod_range_one]))
        (add norm 0 (by grind only [Nat.choose_zero_right]))
        (add norm 0 (by grind only [Finset.prod_empty]))
        (add norm 0 (by grind only [pow_zero]))
        (add norm 0 (by grind only [Nat.choose_self]))
        (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [Nat.factorial_zero]))
        (add norm 0 (by grind only [Finset.prod_singleton]))
        (add norm 0 (by grind only [tsub_zero]))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [ArithmeticFunction.vonMangoldt_apply_one]))
        (add norm 0 (by grind only [sum_bernoulli]))
        (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
        (add norm 0 (by grind only [tsub_self]))
        (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
        (add norm 0 (by grind only [Nat.zero_eq]))
        (add norm 0 (by grind only [MvPolynomial.esymm_zero]))
        (add norm 0 (by grind only [bernsteinPolynomial.sum]))
        (add norm 0 (by grind only [Polynomial.hermite_zero]))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [Nat.Ico_zero_eq_range]))
        (add norm 0 (by grind only [Nat.choose_succ_self]))
        (add norm 0 (by grind only [ArithmeticFunction.sigma_zero_apply_prime_pow]))
        (add norm 0 (by grind only [Nat.centralBinom_zero]))
        (add norm 0 (by grind only [npow_zero]))
        (add norm 0 (by grind only [pow_one]))
        (add norm 0 (by grind only [Finset.range_succ]))
        (add norm 0 (by grind only [Finset.card_range]))
        (add safe 0 (by simp only [Finset.range_one] at *))

    have h_eq : ∑ k ∈ Finset.range 0, k ^ 3 = (∑ k ∈ Finset.range 0, k) ^ 2 := by
      clear * - h_base h_base_sq
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 380
        maxNormIterations := 320
        enableSimp := false
        enableUnfold := false
        })
        (add norm 0 (by ring))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by positivity))
        (add norm 0 (by bound))
        (add norm 100 (by ring_nf))
        (add norm 0 (by split))
        (add norm 1 (by simp))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by omega))
        (add safe 100 (by push_neg))
        (add safe 100 (by interval_cases))
        (add safe 0 (by ext))
        (add safe 0 (by exfalso))
        (add safe 100 (by ring_nf at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Finset.prod_range_zero]))
        (add norm 0 (by grind only [Finset.range_zero]))
        (add norm 0 (by grind only [Nat.choose_zero_right]))
        (add norm 0 (by grind only [Nat.choose_self]))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [tsub_zero]))
        (add norm 0 (by grind only [pow_zero]))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [Finset.prod_range_one]))
        (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
        (add norm 0 (by grind only [tsub_self]))
        (add norm 0 (by grind only [Finset.prod_empty]))
        (add norm 0 (by grind only [Finset.prod_singleton]))
        (add norm 0 (by grind only [Nat.factorial_zero]))
        (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
        (add norm 0 (by grind only [pow_one]))
        (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [Finset.card_range]))
        (add norm 0 (by grind only [ArithmeticFunction.vonMangoldt_apply_one]))
        (add norm 0 (by grind only [sum_bernoulli]))
        (add norm 0 (by grind only [add_pow]))
        (add norm 0 (by grind only [geom_sum₂_with_one]))
        (add norm 0 (by grind only [Finset.range_succ]))
        (add norm 0 (by grind only [Nat.zero_eq]))
        (add norm 0 (by grind only [MvPolynomial.esymm_zero]))
        (add norm 0 (by grind only [Nat.choose_succ_self]))
        (add norm 0 (by grind only [wittPolynomial_eq_sum_C_mul_X_pow]))
        (add norm 0 (by grind only [bernsteinPolynomial.sum]))
        (add norm 0 (by grind only [ArithmeticFunction.sigma_zero_apply_prime_pow]))
        (add norm 0 (by grind only [Nat.Ico_zero_eq_range]))
        (add safe 0 (by simp only [Finset.range_one] at *))

    exact h_eq

  | succ n ih =>
    -- Inductive step: Assume P(n), prove P(n+1)
    -- Informal Step 3: The hypothesis states sum_{k=0}^{n-1} k^3 = (sum_{k=0}^{n-1} k)^2
    -- In Lean, Finset.range n is {0, ..., n-1}. So ih is exactly that.

    -- Informal Step 4: Sum up to n is sum up to n-1 plus n^3
    -- Note: Finset.range (n+1) is {0, ..., n}.
    have h_sum_dec : ∑ k ∈ Finset.range (n + 1), k ^ 3 = (∑ k ∈ Finset.range n, k ^ 3) + n ^ 3 := by
      clear * -
      simp only [Finset.sum_range_succ, add_comm]

    -- Informal Step 5: Substitute IH into the sum decomposition
    have h_sub_IH : ∑ k ∈ Finset.range (n + 1), k ^ 3 = (∑ k ∈ Finset.range n, k) ^ 2 + n ^ 3 := by
      clear * - h_sum_dec ih
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
        (add norm 100 (by push_neg))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 100 (by exfalso))
        (add norm 0 (by simp_all))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by ring_nf at *))
        (add safe 100 (by decide))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [add_pow]))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [Finset.card_range]))
        (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
        (add norm 0 (by grind only [geom_sum_mul_add]))
        (add norm 0 (by grind only [Finset.mul_sum]))
        (add norm 0 (by grind only [Finset.range_succ]))
        (add norm 0 (by grind only [mul_geom_sum]))
        (add norm 0 (by grind only [pow_add]))
        (add norm 0 (by grind only [Finset.range]))
        (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
        (add norm 0 (by grind only [MvPolynomial.NewtonIdentities.esymm_to_weight]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
        (add norm 0 (by grind only [Finset.prod_mul_distrib]))
        (add norm 0 (by grind only [Finset.sum_mul]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
        (add norm 0 (by grind only [sum_range_pow]))
        (add norm 0 (by grind only [mul_comm]))
        (add norm 0 (by grind only [Finset.range_add_one]))
        (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
        (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
        (add norm 0 (by grind only [bernsteinPolynomial.sum_smul]))
        (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
        (add norm 0 (by grind only [numDerangements_sum]))
        (add norm 0 (by grind only [mul_assoc]))
        (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk]))
        (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux1]))
        (add norm 0 (by grind only [bernsteinPolynomial.sum_mul_smul]))

    -- Informal Step 6: Formula for sum of first n integers (0 to n-1)
    -- Sum_{k=0}^{n-1} k = n(n-1)/2
    have h_sum_formula_n : ∑ k ∈ Finset.range n, k = n * (n - 1) / 2 := by
      -- This requires proving the standard arithmetic series formula for Finset.range n
      clear * -
      induction n <;> simp
      try simp [Finset.sum_range_succ, *]
      cases ‹ℕ› <;> simp [Finset.sum] at * <;> ring
      next => ring_nf at *; omega

    -- Informal Step 7: Substitute the formula into our expression
    have h_sub_formula : (∑ k ∈ Finset.range n, k) ^ 2 = (n * (n - 1) / 2) ^ 2 := by
      clear * - h_sum_formula_n
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
        (add norm 0 (by omega))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 100 (by simp))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by exfalso))
        (add safe 100 (by simp_all))
        (add safe 100 (by ring_nf at *))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Finset.card_range]))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [Finset.mul_sum]))
        (add norm 0 (by grind only [Nat.cast_sum]))
        (add norm 0 (by grind only [Finset.prod_mul_distrib]))
        (add norm 0 (by grind only [Finset.prod_const]))
        (add norm 0 (by grind only [mul_pow]))
        (add norm 0 (by grind only [Finset.sum_range_id]))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [mul_geom_sum]))
        (add norm 0 (by grind only [add_pow]))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [Finset.sum_mul]))
        (add norm 0 (by grind only [numDerangements_sum]))
        (add norm 0 (by grind only [Nat.cast_div_charZero]))
        (add norm 0 (by grind only [Finset.prod_pow]))
        (add norm 0 (by grind only [Nat.cast_div]))
        (add norm 0 (by grind only [Nat.mul_div_cancel_left]))
        (add norm 0 (by grind only [bernsteinPolynomial.variance]))
        (add norm 0 (by grind only [div_pow]))
        (add norm 0 (by grind only [Nat.mul_div_left]))
        (add norm 0 (by grind only [Nat.mul_div_cancel]))
        (add norm 0 (by grind only [geom_sum_mul_add]))
        (add norm 0 (by grind only [Finset.range]))
        (add norm 0 (by grind only [geom_sum₂_self]))
        (add norm 0 (by grind only [geom_sum_mul]))
        (add norm 0 (by grind only [Nat.mul_div_right]))
        (add norm 0 (by grind only [geom_sum₂_mul]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
        (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
        (add unsafe 50% (by simp only [pow_two_pow_sub_pow_two_pow]))

    have h_combined : ∑ k ∈ Finset.range (n + 1), k ^ 3 = (n * (n - 1) / 2) ^ 2 + n ^ 3 := by
      clear * - h_sub_IH h_sub_formula
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
        (add safe 0 (by push_neg))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by exfalso))
        (add safe 100 (by simp_all))
        (add safe 100 (by ring_nf at *))
        (add safe 100 (by decide))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
        (add norm 0 (by grind only [add_pow]))
        (add norm 0 (by grind only [Finset.card_range]))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [Finset.range_succ]))
        (add norm 0 (by grind only [geom_sum_mul_add]))
        (add norm 0 (by grind only [mul_geom_sum]))
        (add norm 0 (by grind only [sum_range_pow]))
        (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
        (add norm 0 (by grind only [numDerangements_sum]))
        (add norm 0 (by grind only [Nat.choose_succ_self_right]))
        (add norm 0 (by grind only [Finset.range_add_one]))
        (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
        (add norm 0 (by grind only [Finset.range]))
        (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
        (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
        (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
        (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
        (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk]))
        (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
        (add norm 0 (by grind only [bernsteinPolynomial.sum_smul]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
        (add norm 0 (by grind only [sum_bernoulli]))
        (add norm 0 (by grind only [Finset.prod_pow_choose_succ]))
        (add norm 0 (by grind only [tsub_zero]))
        (add norm 0 (by grind only [numDerangements_succ]))
        (add safe 1 (by simp only [Nat.choose_self] at *))

    -- Informal Steps 8-12: Algebraic manipulation to show it equals (n(n+1)/2)^2
    -- We need to show: (n*(n-1)/2)^2 + n^3 = (n*(n+1)/2)^2

    -- Let's establish the target form first.
    -- Target: (∑ k ∈ Finset.range (n+1), k)^2
    -- First, get the sum formula for range (n+1) which is 0..n
    have h_sum_formula_np1 : ∑ k ∈ Finset.range (n + 1), k = n * (n + 1) / 2 := by
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
        (add norm 0 (by omega))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 1 (by simp))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by exfalso))
        (add safe 100 (by decide))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
        (add norm 0 (by grind only [sum_range_pow]))
        (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [Finset.card_range]))
        (add norm 0 (by grind only [Finset.range_succ]))
        (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
        (add norm 0 (by grind only [Finset.range]))
        (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
        (add norm 0 (by grind only [numDerangements_sum]))
        (add norm 0 (by grind only [Finset.sum_range_id]))
        (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
        (add norm 0 (by grind only [Finset.range_add_one]))
        (add norm 0 (by grind only [Nat.factorial]))
        (add norm 0 (by grind only [numDerangements]))
        (add norm 0 (by grind only [Finset.prod_range_mul_prod_Ico]))
        (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
        (add norm 0 (by grind only [geom_sum_mul_add]))
        (add norm 0 (by grind only [Finset.prod_range_induction]))
        (add norm 0 (by grind only [Finset.range_eq_Ico]))
        (add norm 0 (by grind only [sum_bernoulli]))
        (add norm 0 (by grind only [add_pow]))
        (add norm 0 (by grind only [Finset.prod_range_div']))
        (add norm 0 (by grind only [binomial_sum_eq]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
        (add norm 0 (by grind only [Polynomial.bernoulli_def]))
        (add norm 0 (by grind only [Nat.choose]))
        (add norm 0 (by grind only [Finset.prod_range_div]))
        (add safe 1 (by simp_all only [Nat.prod_range_succ_factorial]))

    have h_target_sq : (∑ k ∈ Finset.range (n + 1), k) ^ 2 = (n * (n + 1) / 2) ^ 2 := by
      clear * - h_sum_formula_np1
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
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by exfalso))
        (add safe 100 (by simp_all))
        (add safe 100 (by ring_nf at *))
        (add safe 100 (by decide))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
        (add norm 0 (by grind only [add_pow]))
        (add norm 0 (by grind only [Finset.range_succ]))
        (add norm 0 (by grind only [Finset.card_range]))
        (add norm 0 (by grind only [Nat.factorial]))
        (add norm 0 (by grind only [geom_sum_mul_add]))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
        (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
        (add norm 0 (by grind only [tsub_zero]))
        (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
        (add norm 0 (by grind only [Nat.choose_succ_self_right]))
        (add norm 0 (by grind only [mul_pow]))
        (add norm 0 (by grind only [Nat.choose_self]))
        (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
        (add norm 0 (by grind only [sum_range_pow]))
        (add norm 0 (by grind only [mul_geom_sum]))
        (add norm 0 (by grind only [Nat.factorial_succ]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
        (add norm 0 (by grind only [numDerangements_succ]))
        (add norm 0 (by grind only [pow_two_pow_sub_pow_two_pow]))
        (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
        (add norm 0 (by grind only [sum_bernoulli]))
        (add norm 0 (by grind only [Finset.range_add_one]))
        (add norm 0 (by grind only [numDerangements_sum]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
        (add norm 0 (by grind only [bernsteinPolynomial.variance]))
        (add norm 0 (by grind only [Finset.mul_sum]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk]))
        (add norm 0 (by grind only [Finset.range]))

    -- Now we need to prove the algebraic identity:
    -- (n * (n - 1) / 2) ^ 2 + n ^ 3 = (n * (n + 1) / 2) ^ 2

    -- To avoid division issues in natural numbers during intermediate steps, 
    -- let's work with the expanded forms or use field_simp/ring if we were in rings.
    -- Since these are naturals, we must be careful with subtraction.
    -- However, the final goal is equality between two specific expressions.

    -- Let's define the LHS and RHS clearly based on previous steps.
    have h_lhs : ∑ k ∈ Finset.range (n + 1), k ^ 3 = (n * (n - 1) / 2) ^ 2 + n ^ 3 := by
      clear * - h_combined
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
        (add norm 1 (by ext))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by omega))
        (add safe 0 (by push_neg))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by exfalso))
        (add safe 100 (by ring_nf at *))
        (add safe 100 (by decide))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
        (add norm 0 (by grind only [add_pow]))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [sum_range_pow]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
        (add norm 0 (by grind only [Finset.range_add_one]))
        (add norm 0 (by grind only [geom_sum_mul_add]))
        (add norm 0 (by grind only [Finset.range_succ]))
        (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
        (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
        (add norm 0 (by grind only [mul_geom_sum]))
        (add norm 0 (by grind only [Finset.prod_range_induction]))
        (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
        (add norm 0 (by grind only [Finset.card_range]))
        (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
        (add norm 0 (by grind only [numDerangements_sum]))
        (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk]))
        (add norm 0 (by grind only [Fin.prod_univ_eq_prod_range]))
        (add norm 0 (by grind only [Finset.prod_flip]))
        (add norm 0 (by grind only [Finset.range]))
        (add norm 0 (by grind only [Polynomial.bernoulli_def]))
        (add norm 0 (by grind only [Finset.sum_range_reflect]))
        (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
        (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
        (add norm 0 (by grind only [binomial_sum_eq]))
        (add norm 0 (by grind only [bernsteinPolynomial.sum_smul]))
        (add norm 0 (by grind only [Finset.prod_range_div']))

    have h_rhs : (∑ k ∈ Finset.range (n + 1), k) ^ 2 = (n * (n + 1) / 2) ^ 2 := by
      clear * - h_target_sq
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
        (add norm 100 (by simp))
        (add norm 0 (by simp_all))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by exfalso))
        (add safe 100 (by ring_nf at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
        (add norm 0 (by grind only [add_pow]))
        (add norm 0 (by grind only [Finset.card_range]))
        (add norm 0 (by grind only [geom_sum_mul_add]))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [Finset.range_succ]))
        (add norm 0 (by grind only [mul_geom_sum]))
        (add norm 0 (by grind only [pow_two_pow_sub_pow_two_pow]))
        (add norm 0 (by grind only [mul_pow]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
        (add norm 0 (by grind only [sum_range_pow]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
        (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
        (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
        (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
        (add norm 0 (by grind only [numDerangements_sum]))
        (add norm 0 (by grind only [Finset.mul_sum]))
        (add norm 0 (by grind only [Nat.factorial]))
        (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
        (add norm 0 (by grind only [Finset.range_add_one]))
        (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
        (add norm 0 (by grind only [bernsteinPolynomial.variance]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
        (add norm 0 (by grind only [Nat.choose_self]))
        (add norm 0 (by grind only [sum_bernoulli]))
        (add norm 0 (by grind only [Finset.range]))
        (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk]))
        (add norm 0 (by grind only [geom_sum₂_self]))
        (add norm 0 (by grind only [Nat.choose_succ_self_right]))

    -- The core algebraic lemma:
    -- For any natural number n, (n*(n-1)/2)^2 + n^3 = (n*(n+1)/2)^2
    -- Note: In Lean, / is integer division. We rely on the fact that n(n-1) is even and n(n+1) is even.

    have h_algebra : (n * (n - 1) / 2) ^ 2 + n ^ 3 = (n * (n + 1) / 2) ^ 2 := by
      -- This is a pure arithmetic fact about naturals.
      clear * -
      cases n
      · simp
      · simp [pow_succ]
        repeat rw [Nat.div_mul_div_comm]
        · zify <;> (ring_nf; omega)
        · obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd ‹_› <;> ring_nf <;> omega
        · obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Nat.even_or_odd ‹_› <;> ring_nf <;> omega
        · obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd ‹_› <;> ring_nf <;> omega
        · obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := Nat.even_or_odd ‹_› <;> ring_nf <;> omega

    -- Combine everything
    have h_final : ∑ k ∈ Finset.range (n + 1), k ^ 3 = (∑ k ∈ Finset.range (n + 1), k) ^ 2 := by
      clear * - h_lhs h_rhs h_algebra
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
        (add norm 0 (by push_neg))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 100 (by exfalso))
        (add norm 0 (by simp_all))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by ring_nf at *))
        (add safe 100 (by decide))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Finset.prod_range_succ']))
        (add norm 0 (by grind only [Finset.prod_range_succ]))
        (add norm 0 (by grind only [Finset.prod_range]))
        (add norm 0 (by grind only [Finset.card_range]))
        (add norm 0 (by grind only [add_pow]))
        (add norm 0 (by grind only [Finset.mul_sum]))
        (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
        (add norm 0 (by grind only [mul_geom_sum]))
        (add norm 0 (by grind only [geom_sum_mul_add]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
        (add norm 0 (by grind only [Finset.range_succ]))
        (add norm 0 (by grind only [Finset.sum_mul]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
        (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
        (add norm 0 (by grind only [Finset.range]))
        (add norm 0 (by grind only [Finset.prod_mul_distrib]))
        (add norm 0 (by grind only [sum_range_pow]))
        (add norm 0 (by grind only [bernsteinPolynomial.sum_smul]))
        (add norm 0 (by grind only [numDerangements_sum]))
        (add norm 0 (by grind only [bernsteinPolynomial.sum_mul_smul]))
        (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
        (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk]))
        (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
        (add norm 0 (by grind only [geom_sum_mul]))
        (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
        (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
        (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
        (add norm 0 (by grind only [Nat.choose_self]))
        (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
        (add norm 0 (by grind only [Nat.choose_succ_self_right]))
        (add norm 0 (by grind only [Finset.prod_const]))
        (add norm 0 (by grind only [Nat.cast_sum]))

    exact h_final
