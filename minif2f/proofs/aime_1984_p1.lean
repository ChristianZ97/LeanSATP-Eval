
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

theorem aime_1984_p1 (u : ℕ → ℚ) (h₀ : ∀ n, u (n + 1) = u n + 1)
    (h₁ : ∑ k ∈ Finset.range 98, u k.succ = 137) : ∑ k ∈ Finset.range 49, u (2 * k.succ) = 93 := by
  have step_sum_split : (∑ k ∈ Finset.range 98, u (k + 1)) = ∑ j ∈ Finset.range 49, (u (2 * j + 1) + u (2 * j + 2)) := by
    clear * - h₁
    have h₂ : (98 : ℕ) = 2 * 49 := by omega
    revert h₁ h₂ u
    aesop  (add simp [Finset.sum_range_succ])
    symm <;> linarith

  have step_recurrence : ∀ j, u (2 * j + 1) = u (2 * j + 2) - 1 := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 1600
      maxNormIterations := 320
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 1 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Nat.fib_two_mul]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [Polynomial.derivative_sq]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [Cardinal.lift_two]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Finset.mulETransformRight.card]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
      (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [Ring.multichoose_two]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [two_ne_zero]))

  have step_substitution : ∑ j ∈ Finset.range 49, (u (2 * j + 1) + u (2 * j + 2)) = ∑ j ∈ Finset.range 49, (2 * u (2 * j + 2) - 1) := by
    clear * - step_sum_split step_recurrence
    simp_rw [step_recurrence] <;> ring_nf

  have step_expansion : ∑ j ∈ Finset.range 49, (2 * u (2 * j + 2) - 1) = 2 * (∑ j ∈ Finset.range 49, u (2 * j + 2)) - 49 := by
    clear * - step_substitution
    simp [Finset.mul_sum, Finset.sum_sub_distrib]

  have step_goal_def : (∑ k ∈ Finset.range 49, u (2 * k.succ)) = ∑ j ∈ Finset.range 49, u (2 * j + 2) := by
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
      (add norm 1 (by ext))
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by exfalso))
      (add safe 100 (by ring_nf at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
      (add norm 0 (by grind only [Finset.range_succ]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [Finset.range_add_one]))
      (add norm 0 (by grind only [sum_range_pow]))
      (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
      (add norm 0 (by grind only [Finset.prod_range_one]))
      (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
      (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
      (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [add_pow]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
      (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
      (add norm 0 (by grind only [Nat.choose_succ_self_right]))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
      (add norm 0 (by grind only [numDerangements]))
      (add norm 0 (by grind only [Finset.prod_range_zero]))
      (add norm 0 (by grind only [geom_sum_mul_add]))
      (add norm 0 (by grind only [Finset.prod_range_mul_prod_Ico]))
      (add norm 0 (by grind only [numDerangements_sum]))
      (add norm 0 (by grind only [Finset.prod_flip]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
      (add norm 0 (by grind only [Finset.prod_range_induction]))
      (add norm 0 (by grind only [Polynomial.bernoulli_def]))
      (add safe 1 (by simp only [Nat.choose_self] at *))

  have step_equation : 137 = 2 * (∑ k ∈ Finset.range 49, u (2 * k.succ)) - 49 := by
    clear * - h₁ step_sum_split step_substitution step_expansion step_goal_def
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 16
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
      (add norm 0 (by grind only [sum_range_pow]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [binomial_sum_eq]))
      (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
      (add norm 0 (by grind only [Finset.prod_range_mul_prod_Ico]))
      (add norm 0 (by grind only [Finset.prod_range_induction]))
      (add norm 0 (by grind only [numDerangements_sum]))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [Finset.prod_range_div]))
      (add norm 0 (by grind only [Finset.prod_range_div']))
      (add norm 0 (by grind only [numDerangements]))
      (add norm 0 (by grind only [Finset.range_succ]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
      (add norm 0 (by grind only [Finset.range_add_one]))
      (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
      (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
      (add norm 0 (by grind only [Finset.sum_range_reflect]))
      (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
      (add norm 0 (by grind only [Finset.range_eq_Ico]))
      (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
      (add norm 0 (by grind only [Finset.prod_flip]))
      (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
      (add norm 0 (by rw [Real.BohrMollerup.f_add_nat_eq]))
      (add norm 0 (by grind only [Polynomial.bernoulli_def]))
      (add norm 0 (by grind only [add_pow]))
      (add norm 0 (by grind only [Finset.prod_range_diag_flip]))

  have step_solve : 2 * (∑ k ∈ Finset.range 49, u (2 * k.succ)) = 186 := by
    clear * - step_equation
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 16
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 1 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
      (add norm 0 (by grind only [Finset.range_add_one]))
      (add norm 0 (by grind only [Finset.prod_range_one]))
      (add norm 0 (by grind only [numDerangements]))
      (add norm 0 (by grind only [Nat.choose_self]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [sum_range_pow]))
      (add norm 0 (by grind only [bernsteinPolynomial.sum]))
      (add norm 0 (by grind only [Eq.symm]))
      (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
      (add norm 0 (by grind only [Nat.choose_succ_self_right]))
      (add norm 0 (by grind only [Finset.range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_induction]))
      (add norm 0 (by grind only [Finset.prod_flip]))
      (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Finset.prod_range_zero]))
      (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
      (add norm 0 (by grind only [Polynomial.bernoulli_def]))
      (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
      (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
      (add norm 0 (by grind only [Polynomial.bernoulli]))
      (add norm 0 (by grind only [Nat.choose_one_right]))
      (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
      (add norm 0 (by grind only [add_pow]))
      (add norm 0 (by grind only [Nat.choose_succ_self]))

  have step_final : ∑ k ∈ Finset.range 49, u (2 * k.succ) = 93 := by
    clear * - step_solve
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 100 (by simp_all))
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
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Finset.range_add_one]))
      (add norm 0 (by grind only [Finset.prod_range_one]))
      (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
      (add norm 0 (by grind only [sum_range_pow]))
      (add norm 0 (by grind only [Finset.range_succ]))
      (add norm 0 (by grind only [Finset.prod_flip]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [numDerangements]))
      (add norm 0 (by grind only [Finset.prod_range_induction]))
      (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [Finset.prod_range_zero]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
      (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
      (add norm 0 (by grind only [Nat.choose_self]))
      (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
      (add norm 0 (by grind only [Finset.self_mem_range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_div']))
      (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
      (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
      (add norm 0 (by grind only [Nat.sum_range_choose]))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [Finset.eq_prod_range_div]))
      (add norm 0 (by grind only [Nat.choose_succ_self_right]))
      (add norm 0 (by grind only [geom_sum_mul_add]))
      (add norm 0 (by grind only [dist_partial_sum']))
      (add norm 0 (by grind only [Polynomial.bernoulli_def]))
      (add norm 0 (by grind only [dist_partial_sum]))
      (add norm 0 (by grind only [Finset.range_one]))

  exact step_final
