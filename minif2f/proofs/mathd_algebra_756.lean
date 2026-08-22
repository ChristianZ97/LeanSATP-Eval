
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

theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  -- Step 1: 2^a = 32
  have h_step1 : (2 : ℝ) ^ a = 32 := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [ENNReal.two_ne_top]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [ENNReal.rpow_two] at *))
      (add unsafe 90% (by simp only [Complex.cpow_two] at *))
      (add unsafe 90% (by simp only [NNReal.rpow_two] at *))

  -- Step 2: 2^a = 2^5
  have h_step2 : (2 : ℝ) ^ a = (2 : ℝ) ^ (5 : ℝ) := by
    have h_pow5 : (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) := by norm_num
    rw [h_pow5] at h_step1
    exact h_step1

  -- Step 3: a = 5
  have h_a_eq_5 : a = (5 : ℝ) := by
    simp_all [Real.rpow_def_of_pos]
    have h_log := congr_arg Real.log h_step2
    simp [show (32 : ℝ) = 2 ^ 5 by norm_cast, Real.log_pow] at h_log
    all_goals nlinarith [Real.log_pos one_lt_two]

  -- Step 4: a^b = 125
  have h_step4 : a ^ b = (125 : ℝ) := by
    clear * - h₁
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
      (add norm 0 (by grind only [sq_eq_sq_iff_eq_or_eq_neg]))
      (add norm 0 (by grind only [Real.rpow_def_of_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_eq_iff_sq_eq]))
      (add norm 0 (by grind only [Quaternion.normSq_coe]))
      (add norm 0 (by grind only [Hyperreal.coe_eq_coe]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Quaternion.inner_self]))
      (add norm 0 (by grind only [Real.arsinh]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by rw [Quaternion.coe_one]))
      (add norm 0 (by grind only [Quaternion.sq_eq_neg_normSq]))
      (add norm 0 (by grind only [EReal.coe_mul]))
      (add norm 0 (by grind only [Real.log_pow]))
      (add norm 0 (by grind only [Complex.arg_real_mul]))
      (add norm 0 (by grind only [Real.ofCauchy_one]))
      (add norm 0 (by grind only [Real.rpow_def]))
      (add norm 0 (by grind only [integral_gaussian]))
      (add norm 0 (by grind only [Quaternion.star_coe]))
      (add norm 0 (by rw [Quaternion.coe_mul]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [sq_lt_one_iff]))
      (add norm 0 (by grind only [sq_eq_sq_iff_abs_eq_abs]))
      (add norm 0 (by grind only [Quaternion.star_mul_self]))
      (add norm 0 (by grind only [Quaternion.normSq_exp]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  -- Step 5: 5^b = 125
  have h_step5 : (5 : ℝ) ^ b = (125 : ℝ) := by
    rw [h_a_eq_5] at h_step4
    exact h_step4

  -- Step 6: 5^b = 5^3
  have h_step6 : (5 : ℝ) ^ b = (5 : ℝ) ^ (3 : ℝ) := by
    have h_pow3 : (125 : ℝ) = (5 : ℝ) ^ (3 : ℝ) := by norm_num
    rw [h_pow3] at h_step5
    exact h_step5

  -- Step 7: b = 3
  have h_b_eq_3 : b = (3 : ℝ) := by
    aesop  (add simp [Real.rpow_def_of_pos])
    have h := congr_arg Real.log h_step4
    simp [show (125 : ℝ) = 5 ^ 3 by norm_cast] at h
    nlinarith [mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 5)) (show (0 : ℝ) < 5 by norm_num)]

  -- Step 8: b^a = 3^5
  have h_step8 : b ^ a = (3 : ℝ) ^ (5 : ℝ) := by
    rw [h_b_eq_3, h_a_eq_5]

  -- Step 9: b^a = 243
  have h_step9 : b ^ a = (243 : ℝ) := by
    have h_final : (3 : ℝ) ^ (5 : ℝ) = (243 : ℝ) := by norm_num
    rw [h_step8, h_final]

  exact h_step9
