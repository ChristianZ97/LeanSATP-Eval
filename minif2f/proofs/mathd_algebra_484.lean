
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

theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  -- Step 1: Express 27 as 3^3
  have h1 : (27 : ℝ) = (3 : ℝ) ^ 3 := by
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
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Nat.superFactorial_two_mul]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by rw [Nat.cast_ofNat]))
      (add norm 0 (by grind only [Polynomial.derivative_sq]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Nat.sqrt_eq']))
      (add norm 0 (by grind only [Cardinal.lift_two]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add unsafe 90% (by simp only [Nat.cast_two] at *))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Complex.cpow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
      (add unsafe 90% (by simp only [ENNReal.rpow_two] at *))

  -- Step 2: Use logarithm power rule: ln(3^3) = 3 * ln(3)
  have h2 : Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ 3) := by
    clear * - h1
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by simp_all))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [ArithmeticFunction.log_apply]))
      (add norm 0 (by grind only [Stirling.log_stirlingSeq_formula]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Real.Gamma_pos_of_pos]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Real.log]))
      (add norm 0 (by grind only [Real.rpow_natCast]))
      (add norm 0 (by grind only [padicValRat_two_harmonic]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.BohrMollerup.tendsto_log_gamma]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [Real.BohrMollerup.f_nat_eq]))
      (add norm 0 (by grind only [Real.Gamma]))
      (add norm 0 (by grind only [Real.doublingGamma]))
      (add norm 0 (by grind only [Behrend.nValue_pos]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by rw [Complex.natCast_log]))
      (add norm 0 (by grind only [Real.exp_half]))
      (add norm 0 (by grind only [integral_inv_of_pos]))
      (add norm 0 (by grind only [Real.rpow_pos_of_pos]))
      (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half]))
      (add safe 100 (by simp [Real.log_pow] at *))
      (add safe 100 (by simp [Real.log_mul] at *))
      (add safe 100 (by simp [Real.log_rpow] at *))
      (add safe 100 (by simp [Real.log_div] at *))
      (add safe 100 (by simp [Behrend.nValue] at *))
      (add safe 100 (by simp [Behrend.dValue] at *))
      (add unsafe 10% (by grind only [Real.log_pos]))
      (add unsafe 10% (by grind only [Complex.log_ofReal_mul]))
      (add unsafe 10% (by grind only [Real.Gamma_mul_Gamma_add_half_of_pos]))

  have h3 : Real.log ((3 : ℝ) ^ 3) = 3 * Real.log (3 : ℝ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.log_pow]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [Real.Gamma_pos_of_pos]))
      (add norm 0 (by grind only [Stirling.log_stirlingSeq_formula]))
      (add norm 0 (by grind only [Complex.log_ofReal_mul]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [Real.log]))
      (add norm 0 (by grind only [ArithmeticFunction.log_apply]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Real.rpow_pos_of_pos]))
      (add norm 0 (by grind only [Real.doublingGamma]))
      (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half_of_pos]))
      (add norm 0 (by grind only [Real.rpow_natCast]))
      (add norm 0 (by grind only [Real.Gamma]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.BohrMollerup.tendsto_log_gamma]))
      (add norm 0 (by grind only [Real.rpow_logb]))
      (add norm 0 (by grind only [Real.exp_half]))
      (add norm 0 (by grind only [Real.rpow_def_of_pos]))
      (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half]))
      (add norm 0 (by grind only [Real.exp_log]))
      (add norm 0 (by grind only [Real.sqrt_pos]))
      (add norm 0 (by grind only [Real.Gamma_one_half_eq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.Gamma_eq_integral]))
      (add norm 0 (by grind only [integral_inv_of_pos]))
      (add safe 100 (by simp [Real.log_rpow] at *))
      (add safe 100 (by simp [Real.log_mul] at *))
      (add safe 100 (by simp [Real.log_div] at *))
      (add safe 100 (by simp [Behrend.nValue] at *))
      (add unsafe 50% (by nlinarith [Real.log_pos]))

  -- Step 3: Substitute back into the expression
  have h4 : Real.log (27 : ℝ) = 3 * Real.log (3 : ℝ) := by
    clear * - h2 h3
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.log_pow]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [Real.Gamma_pos_of_pos]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [Complex.log_ofReal_mul]))
      (add norm 0 (by grind only [Real.log]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Real.Gamma]))
      (add norm 0 (by grind only [Stirling.log_stirlingSeq_formula]))
      (add norm 0 (by grind only [Real.rpow_natCast]))
      (add norm 0 (by grind only [Real.rpow_pos_of_pos]))
      (add norm 0 (by grind only [Real.exp_log]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.log_pos]))
      (add norm 0 (by grind only [Real.doublingGamma]))
      (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half_of_pos]))
      (add norm 0 (by grind only [Behrend.nValue_pos]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [Real.exp_half]))
      (add norm 0 (by grind only [Real.rpow_def_of_pos]))
      (add norm 0 (by grind only [Real.BohrMollerup.tendsto_log_gamma]))
      (add norm 0 (by grind only [Real.sqrt_pos]))
      (add norm 0 (by grind only [Real.Gamma_eq_integral]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [ArithmeticFunction.log_apply]))
      (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half]))
      (add norm 0 (by grind only [Stirling.stirlingSeq]))
      (add norm 0 (by grind only [Real.rpow_mul]))
      (add safe 100 (by simp [Real.log_mul] at *))
      (add safe 100 (by simp [Real.log_rpow] at *))
      (add safe 100 (by simp [Real.log_div] at *))
      (add safe 100 (by simp [Behrend.nValue] at *))

  -- Step 4: Divide both sides by ln(3)
  -- Note: We need to ensure ln(3) ≠ 0. Since 3 > 1, ln(3) > 0.
  have h5 : Real.log (3 : ℝ) ≠ 0 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
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
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.doublingGamma]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [Real.log]))
      (add norm 0 (by grind only [Stirling.log_stirlingSeq_formula]))
      (add norm 0 (by grind only [Real.BohrMollerup.tendsto_log_gamma]))
      (add norm 0 (by grind only [Real.Gamma]))
      (add norm 0 (by grind only [Real.Gamma_eq_integral]))
      (add norm 0 (by grind only [Real.Gamma_one_half_eq]))
      (add norm 0 (by grind only [ArithmeticFunction.log_apply]))
      (add norm 0 (by grind only [integral_inv_of_pos]))
      (add norm 0 (by grind only [Real.Gamma_one]))
      (add norm 0 (by grind only [Real.doublingGamma_eq_Gamma]))
      (add norm 0 (by grind only [Real.sqrt_pos]))
      (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half]))
      (add norm 0 (by grind only [Real.log_two_lt_d9]))
      (add norm 0 (by grind only [Real.Gamma_ne_zero]))
      (add norm 0 (by grind only [mellin_inversion]))
      (add norm 0 (by grind only [mellinInv_eq_fourierIntegralInv]))
      (add norm 0 (by grind only [Real.log_one]))
      (add norm 0 (by grind only [Behrend.nValue_pos]))
      (add norm 0 (by grind only [Real.rpow_logb]))
      (add safe 100 (by simp [Real.log_mul] at *))
      (add safe 100 (by simp [Real.log_pow] at *))
      (add safe 100 (by simp [Real.log_div] at *))
      (add unsafe 10% (by grind only [Real.log_rpow]))
      (add unsafe 10% (by grind only [Real.Gamma_pos_of_pos]))
      (add unsafe 10% (by grind only [Real.Gamma_add_one]))
      (add unsafe 10% (by grind only [Real.log_pos]))
      (add unsafe 10% (by grind only [Complex.log_ofReal_mul]))
      (add unsafe 10% (by grind only [Real.Gamma_mul_Gamma_add_half_of_pos]))
      (add unsafe 10% (by grind only [Real.rpow_pos_of_pos]))
      (add unsafe 50% (by nlinarith [Real.b_pos]))

  -- Step 5: Final computation
  have h6 : Real.log (27 : ℝ) / Real.log (3 : ℝ) = (3 * Real.log (3 : ℝ)) / Real.log (3 : ℝ) := by
    clear * - h4
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.log_mul]))
      (add norm 0 (by grind only [Real.log_rpow]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [Real.log]))
      (add norm 0 (by grind only [Real.log_pow]))
      (add norm 0 (by grind only [Real.Gamma_pos_of_pos]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [Real.Gamma]))
      (add norm 0 (by grind only [Real.doublingGamma]))
      (add norm 0 (by grind only [Stirling.log_stirlingSeq_formula]))
      (add norm 0 (by grind only [Real.rpow_sub]))
      (add norm 0 (by grind only [Real.div_sqrt]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.BohrMollerup.tendsto_log_gamma]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [Real.rpow_add]))
      (add norm 0 (by grind only [Real.log_pos]))
      (add safe 0 (by simp only [Real.log_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [Complex.log_ofReal_mul] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))

  have h7 : (3 * Real.log (3 : ℝ)) / Real.log (3 : ℝ) = (3 : ℝ) := by
    clear * - h5
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 120
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.log_mul]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [Real.log_rpow]))
      (add norm 0 (by grind only [Real.log_pow]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [Stirling.log_stirlingSeq_formula]))
      (add norm 0 (by grind only [Real.log]))
      (add norm 0 (by grind only [Real.Gamma_pos_of_pos]))
      (add norm 0 (by grind only [Real.doublingGamma]))
      (add norm 0 (by grind only [Real.Gamma]))
      (add norm 0 (by grind only [Real.div_sqrt]))
      (add norm 0 (by grind only [Real.rpow_sub]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Stirling.stirlingSeq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [Real.log_div] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [Complex.log_ofReal_mul] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))

  have h8 : Real.log (27 : ℝ) / Real.log (3 : ℝ) = (3 : ℝ) := by
    clear * - h6 h7
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.log_mul]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [Real.log]))
      (add norm 0 (by grind only [Real.Gamma_pos_of_pos]))
      (add norm 0 (by grind only [Real.log_pow]))
      (add norm 0 (by grind only [Complex.log_ofReal_mul]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [Stirling.log_stirlingSeq_formula]))
      (add norm 0 (by grind only [Real.doublingGamma]))
      (add norm 0 (by grind only [Real.Gamma]))
      (add norm 0 (by grind only [Real.BohrMollerup.tendsto_log_gamma]))
      (add norm 0 (by grind only [Real.log_pos]))
      (add norm 0 (by grind only [integral_inv_of_pos]))
      (add norm 0 (by grind only [Real.div_sqrt]))
      (add norm 0 (by grind only [Real.rpow_sub]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.rpow_pos_of_pos]))
      (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half_of_pos]))
      (add norm 0 (by grind only [Real.Gamma_one]))
      (add norm 0 (by grind only [ArithmeticFunction.log_apply]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Real.log_one]))
      (add norm 0 (by grind only [integral_log_of_pos]))
      (add norm 0 (by grind only [Real.sqrt_pos]))
      (add safe 100 (by simp [Real.log_div] at *))
      (add safe 100 (by simp [Real.log_rpow] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add unsafe 10% (by grind only [ne_of_gt]))

  exact h8
