
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

theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 (r : ℝ)
    (h₀ : r ^ ((1 : ℝ) / 3) + 1 / r ^ ((1 : ℝ) / 3) = 3)
    (h₁ : 0 < r) : r ^ 3 + 1 / r ^ 3 = 5778 := by
  -- Step 1: Let x = r^(1/3). Then x + 1/x = 3.
  let x := r ^ ((1 : ℝ) / 3)
  have h₂ : x + 1 / x = 3 := by
    clear * - h₀ h₁
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 120
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [Real.rpow_one]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [Real.doublingGamma]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [Real.rpow_sub']))
      (add norm 0 (by grind only [Real.rpow_add]))
      (add norm 0 (by grind only [Real.rpow_mul]))
      (add norm 0 (by grind only [ne_of_gt]))
      (add norm 0 (by grind only [Real.log_div]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.rpow_neg_one]))
      (add norm 0 (by grind only [one_half_pos]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [integral_one_div_of_pos]))
      (add norm 0 (by grind only [Real.Gamma]))
      (add norm 0 (by grind only [Real.Gamma_one]))
      (add norm 0 (by grind only [mul_inv_cancel]))
      (add norm 0 (by grind only [Real.rpow_pos_of_pos]))
      (add norm 0 (by grind only [Real.conjExponent]))
      (add norm 0 (by grind only [WeakFEPair.h_feq']))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [Real.div_rpow] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 1 (by unfold div_le_iff'))
      (add unsafe 90% (by simp only [Real.rpow_sub]))

  -- Step 2 & 3 & 4: Compute x^2 + 1/x^2 = 7.
  have h₃ : x ^ 2 + 1 / x ^ 2 = 7 := by
    -- (x + 1/x)^2 = x^2 + 2 + 1/x^2 = 9 => x^2 + 1/x^2 = 7
    have h₄ : (x + 1 / x) ^ 2 = 9 := by
      clear * - h₂
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        enableSimp := false
        enableUnfold := false
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by bound))
        (add norm 1 (by field_simp [*] at *))
        (add norm 1 (by norm_num [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 0 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 50% (by ring_nf at *))
        (add norm 0 (by grind only [two_ne_zero]))
        (add norm 0 (by grind only [one_div]))
        (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
        (add norm 0 (by grind only [Real.Gamma_two]))
        (add norm 0 (by grind only [even_two]))
        (add norm 0 (by grind only [div_pow]))
        (add norm 0 (by grind only [sq_sub_sq]))
        (add norm 0 (by grind only [Real.sq_sqrt]))
        (add norm 0 (by grind only [zero_lt_two]))
        (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
        (add norm 0 (by grind only [two_ne_zero']))
        (add norm 0 (by grind only [integral_id]))
        (add norm 0 (by grind only [mul_pow]))
        (add norm 0 (by grind only [mul_one_div]))
        (add norm 0 (by grind only [Nat.cast_two]))
        (add norm 0 (by grind only [Complex.ofReal_ofNat]))
        (add norm 0 (by grind only [Real.doublingGamma]))
        (add norm 0 (by grind only [integral_gaussian]))
        (add norm 0 (by grind only [neg_sq]))
        (add norm 0 (by grind only [ENNReal.rpow_two]))
        (add norm 0 (by grind only [mul_one]))
        (add norm 0 (by grind only [Real.sqrt_sq]))
        (add norm 0 (by grind only [zero_le_two]))
        (add norm 0 (by grind only [goldenConj]))
        (add norm 0 (by grind only [Real.rpow_one]))
        (add norm 0 (by grind only [one_mul]))
        (add norm 0 (by grind only [one_pow]))
        (add norm 0 (by grind only [Real.Gamma_add_one]))
        (add safe 0 (by simp only [div_self] at *))
        (add safe 0 (by simp only [mul_div_cancel₀] at *))
        (add unsafe 90% (by simp only [Real.rpow_two] at *))
        (add unsafe 90% (by simp only [pow_two] at *))

    have h₅ : x ^ 2 + 2 + 1 / x ^ 2 = 9 := by
      clear * - h₄ h₁
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        maxGoals := 512
        enableSimp := false
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by bound))
        (add norm 100 (by simp_all))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 0 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 10% (by exfalso))
        (add unsafe 50% (by ring_nf at *))
        (add norm 0 (by grind only [one_div]))
        (add norm 0 (by grind only [two_ne_zero]))
        (add norm 0 (by grind only [Real.Gamma_two]))
        (add norm 0 (by grind only [Real.rpow_one]))
        (add norm 0 (by grind only [zero_lt_two]))
        (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
        (add norm 0 (by grind only [mul_one_div]))
        (add norm 0 (by grind only [zero_le_two]))
        (add norm 0 (by grind only [div_pow]))
        (add norm 0 (by grind only [even_two]))
        (add norm 0 (by grind only [Real.rpow_sub]))
        (add norm 0 (by grind only [Real.rpow_mul]))
        (add norm 0 (by grind only [Real.doublingGamma]))
        (add norm 0 (by grind only [Real.Gamma_add_one]))
        (add norm 0 (by grind only [Real.rpow_pos_of_pos]))
        (add norm 0 (by grind only [Real.rpow_natCast]))
        (add norm 0 (by grind only [Real.Gamma]))
        (add norm 0 (by grind only [one_half_pos]))
        (add norm 0 (by grind only [Real.sq_sqrt]))
        (add norm 0 (by grind only [Real.Gamma_one]))
        (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half_of_pos]))
        (add norm 0 (by grind only [sq_pos_of_pos]))
        (add norm 0 (by grind only [zero_lt_two']))
        (add norm 0 (by grind only [Real.Gamma_one_half_eq]))
        (add norm 0 (by grind only [Real.log_rpow]))
        (add norm 0 (by grind only [ne_of_gt]))
        (add norm 0 (by grind only [Real.Gamma_pos_of_pos]))
        (add norm 0 (by grind only [two_ne_zero']))
        (add norm 0 (by grind only [div_one]))
        (add safe 0 (by simp only [div_self] at *))
        (add safe 0 (by simp only [mul_div_cancel₀] at *))
        (add unsafe 50% (by simp only [sq_sub_sq]))

    have h₆ : x ^ 2 + 1 / x ^ 2 = 7 := by
      clear * - h₅
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 520
        enableSimp := false
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by bound))
        (add norm 100 (by simp_all))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 0 (by omega))
        (add safe 100 (by push_neg))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 10% (by exfalso))
        (add unsafe 50% (by ring_nf at *))
        (add norm 0 (by grind only [zero_lt_two]))
        (add norm 0 (by grind only [two_ne_zero]))
        (add norm 0 (by grind only [even_two]))
        (add norm 0 (by grind only [Real.Gamma_two]))
        (add norm 0 (by grind only [one_div]))
        (add norm 0 (by grind only [sq_pos_of_pos]))
        (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
        (add norm 0 (by grind only [div_pow]))
        (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
        (add norm 0 (by grind only [Nat.cast_two]))
        (add norm 0 (by grind only [Real.sq_sqrt]))
        (add norm 0 (by grind only [zero_lt_two']))
        (add norm 0 (by grind only [Real.rpow_natCast]))
        (add norm 0 (by grind only [pow_pos]))
        (add norm 0 (by grind only [one_half_pos]))
        (add norm 0 (by grind only [integral_id]))
        (add norm 0 (by grind only [zero_le_two]))
        (add norm 0 (by grind only [sub_sq]))
        (add norm 0 (by grind only [mul_one_div]))
        (add norm 0 (by grind only [Real.sqrt_lt]))
        (add norm 0 (by grind only [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq]))
        (add norm 0 (by grind only [Real.sqrt_sq]))
        (add norm 0 (by grind only [ENNReal.ofReal_pow]))
        (add norm 0 (by grind only [goldenRatio]))
        (add norm 0 (by simp_all only [Nat.cast_ofNat]))
        (add norm 0 (by grind only [goldenConj]))
        (add norm 0 (by grind only [Stirling.stirlingSeq]))
        (add safe 0 (by simp only [div_self] at *))
        (add unsafe 50% (by simp only [sq_sub_sq]))
        (add unsafe 90% (by simp only [Real.rpow_two] at *))
        (add unsafe 90% (by simp only [pow_two] at *))
        (add unsafe 90% (by simp only [ENNReal.rpow_two] at *))

    exact h₆

  -- Step 5 & 6 & 7 & 8: Compute r + 1/r = 18.
  -- Note that r = x^3. So we need x^3 + 1/x^3.
  -- Identity: (x + 1/x)^3 = x^3 + 1/x^3 + 3(x + 1/x)
  have h₇ : x ^ 3 + 1 / x ^ 3 = 18 := by
    have h₈ : (x + 1 / x) ^ 3 = 27 := by
      clear * - h₂
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        enableSimp := false
        enableUnfold := false
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by bound))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 0 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 50% (by ring_nf at *))
        (add norm 0 (by grind only [one_div]))
        (add norm 0 (by grind only [two_ne_zero]))
        (add norm 0 (by grind only [Real.Gamma_two]))
        (add norm 0 (by grind only [even_two]))
        (add norm 0 (by grind only [mul_one]))
        (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
        (add norm 0 (by grind only [one_mul]))
        (add norm 0 (by grind only [mul_one_div]))
        (add norm 0 (by grind only [two_ne_zero']))
        (add norm 0 (by grind only [mul_pow]))
        (add norm 0 (by grind only [Complex.ofReal_ofNat]))
        (add norm 0 (by grind only [one_pow]))
        (add norm 0 (by grind only [div_pow]))
        (add norm 0 (by grind only [div_one]))
        (add norm 0 (by grind only [sq_sub_sq]))
        (add norm 0 (by grind only [Complex.ofReal_one]))
        (add norm 0 (by grind only [Real.rpow_one]))
        (add norm 0 (by grind only [goldenConj]))
        (add norm 0 (by grind only [integral_id]))
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [neg_sq]))
        (add norm 0 (by grind only [zero_lt_two]))
        (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
        (add norm 0 (by grind only [Real.sq_sqrt]))
        (add norm 0 (by rw [Quaternion.coe_one]))
        (add norm 0 (by grind only [Complex.ofReal_pow]))
        (add norm 0 (by grind only [Complex.ofReal_sub]))
        (add safe 0 (by simp only [div_self] at *))
        (add safe 0 (by simp only [mul_div_assoc] at *))
        (add safe 0 (by simp only [mul_div_cancel₀] at *))
        (add safe 0 (by simp only [Complex.Gamma_one_half_eq] at *))
        (add safe 0 (by simp only [Complex.ofReal_div] at *))

    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [one_half_pos]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [Real.rpow_pos_of_pos]))
      (add norm 0 (by grind only [Real.rpow_natCast]))
      (add norm 0 (by grind only [pow_pos]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [Real.log_div]))
      (add norm 0 (by grind only [Real.log_rpow]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by simp_all only [mul_lt_mul_left]))
      (add norm 0 (by grind only [CircleDeg1Lift.transnumAuxSeq_dist_lt]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [one_div_one]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Real.doublingGamma]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [goldenRatio]))
      (add norm 0 (by grind only [Real.rpow_mul]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add unsafe 90% (by simp only [Real.rpow_sub]))
      (add unsafe 10% (by grind only [Real.rpow_one]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by simp only [sq_sub_sq]))
      (add unsafe 10% (by grind only [ne_of_gt]))

  -- We know r = x^3. So r + 1/r = x^3 + 1/x^3 = 18.
  have h₈ : r + 1 / r = 18 := by
    have h₉ : r = x ^ 3 := by
      -- r = r^1 = (r^(1/3))^3 = x^3
      have h₁₀ : x = r ^ ((1 : ℝ) / 3) := rfl
      calc
        r = (r ^ ((1 : ℝ) / 3)) ^ 3 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h₁.le]
          norm_num

        _ = x ^ 3 := by rw [← h₁₀]

    have h₁₀ : 1 / r = 1 / (x ^ 3) := by
      rw [h₉]

    have h₁₁ : r + 1 / r = x ^ 3 + 1 / x ^ 3 := by
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        maxGoals := 512
        enableSimp := false
        enableUnfold := false
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 100 (by simp_all))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 0 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 10% (by exfalso))
        (add norm 0 (by grind only [one_div]))
        (add norm 0 (by grind only [mul_one_div]))
        (add norm 0 (by grind only [two_ne_zero]))
        (add norm 0 (by grind only [Real.Gamma_two]))
        (add norm 0 (by grind only [Real.rpow_one]))
        (add norm 0 (by grind only [zero_lt_two]))
        (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
        (add norm 0 (by rw [mul_one]))
        (add norm 0 (by grind only [two_ne_zero']))
        (add norm 0 (by rw [one_mul]))
        (add norm 0 (by grind only [mul_inv_cancel]))
        (add norm 0 (by grind only [one_half_pos]))
        (add norm 0 (by grind only [Real.Gamma_add_one]))
        (add norm 0 (by grind only [Real.log_div]))
        (add norm 0 (by grind only [div_one]))
        (add norm 0 (by grind only [even_two]))
        (add norm 0 (by grind only [Real.rpow_mul]))
        (add norm 0 (by grind only [Real.doublingGamma]))
        (add norm 0 (by grind only [div_pow]))
        (add norm 0 (by grind only [neg_div]))
        (add safe 0 (by simp only [div_self] at *))
        (add safe 0 (by simp only [mul_div_cancel₀] at *))
        (add safe 0 (by simp only [mul_div_assoc] at *))
        (add safe 0 (by simp only [sub_div] at *))
        (add safe 0 (by simp only [div_div] at *))
        (add safe 0 (by simp only [div_mul_cancel₀] at *))
        (add safe 0 (by simp only [mul_div] at *))
        (add safe 1 (by unfold mul_le_mul_left))
        (add safe 1 (by unfold div_le_iff))
        (add safe 1 (by unfold le_div_iff))
        (add unsafe 90% (by simp only [Real.rpow_sub]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_left]))

    have h₁₂ : x ^ 3 + 1 / x ^ 3 = 18 := h₇
    rw [h₁₁]
    exact h₁₂

  -- Step 9 & 10 & 11 & 12: Compute r^3 + 1/r^3.
  -- We have y = r + 1/r = 18.
  -- We want r^3 + 1/r^3.
  -- Identity: (r + 1/r)^3 = r^3 + 1/r^3 + 3(r + 1/r)
  have h₉ : r ^ 3 + 1 / r ^ 3 = 5778 := by
    have h₁₀ : (r + 1 / r) ^ 3 = 18 ^ 3 := by
      rw [h₈]

    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [mul_div_cancel₀]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [Real.rpow_sub]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [div_mul]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [div_sub']))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 1 (by unfold mul_le_mul_left))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold mul_le_mul_right))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))

  exact h₉
