
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

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  -- Step 1: (a - 1)^2 >= 0
  have h1 : (a - 1 : ℝ) ^ 2 ≥ 0 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
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
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [div_le_self_iff]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [integral_id]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [pow_left_strictMonoOn]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [Real.sin_sq_le_one]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [div_le_one']))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [Real.sin_sq]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [inv_nonneg]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))

  -- Step 2: Expand (a - 1)^2 to get a^2 - 2a + 1 >= 0
  have h2 : a ^ 2 - 2 * a + 1 ≥ 0 := by
    clear * - h1
    aesop (config := {
      maxRuleApplications := 100
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
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [mul_le_mul_right]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [pow_pos]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [integral_id]))
      (add norm 0 (by grind only [Real.sin_sq]))
      (add norm 0 (by grind only [div_le_one]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add unsafe 50% (by simp only [sq_sub_sq]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))

  -- Step 3: Rearrange to get 1 >= 2a - a^2
  have h3 : 1 ≥ 2 * a - a ^ 2 := by
    clear * - h2
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 600
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
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [le_mul_of_one_le_left']))
      (add norm 0 (by grind only [one_le_pow_of_one_le]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by simp only [Int.le_self_sq]))
      (add unsafe 50% (by simp only [sq_sub_sq]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))

  -- Step 4: Factor right side to get 1 >= a(2 - a)
  have h4 : 1 ≥ a * (2 - a) := by
    clear * - h3
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
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [le_div_iff]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by rw [one_mul]))
      (add unsafe 90% (by simp only [zero_le_two] at *))
      (add unsafe 90% (by simp only [mul_le_mul_left] at *))
      (add unsafe 90% (by simp only [mul_le_mul_right] at *))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))

  -- Step 5: Conclude a(2 - a) <= 1
  have h5 : a * (2 - a) ≤ 1 := by
    clear * - h4
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [sq_nonneg]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [Real.two_le_pi]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [one_le_two]))
      (add unsafe 50% (by nlinarith [Real.logb_le_logb]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [unitInterval.le_one]))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_right']))
      (add unsafe 50% (by nlinarith [div_nonneg]))

  exact h5
