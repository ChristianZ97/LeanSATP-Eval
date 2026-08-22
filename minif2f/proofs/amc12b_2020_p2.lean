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


theorem amc12b_2020_p2 :
    (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) =
      1 := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 10
    maxNormIterations := 520
    enableSimp := false
    enableUnfold := false
    })
    (add norm 0 (by ring))
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by field_simp [*] at *))
    (add norm 1 (by norm_num [*] at *))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 1 (by ring_nf at *))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 10% (by exfalso))
    (add norm 0 (by grind only [div_pow]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [even_two]))
    (add norm 0 (by grind only [neg_sq]))
    (add norm 0 (by grind only [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq]))
    (add norm 0 (by grind only [integral_id]))
    (add norm 0 (by grind only [sub_sq]))
    (add norm 0 (by grind only [mul_pow]))
    (add norm 0 (by grind only [quadraticChar_sq_one]))
    (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
    (add norm 0 (by grind only [sq_eq_zero_iff]))
    (add norm 0 (by grind only [neg_one_sq]))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
    (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
    (add norm 0 (by grind only [sum_four_sq_mul_sum_four_sq]))
    (add norm 0 (by grind only [goldenConj]))
    (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
    (add safe 0 (by simp only [div_self] at *))
    (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
    (add safe 0 (by simp only [two_ne_zero'] at *))
    (add safe 0 (by simp only [sub_div] at *))
    (add safe 0 (by simp only [mul_div_mul_left] at *))
    (add safe 0 (by simp only [eq_div_iff] at *))
    (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
    (add safe 0 (by simp only [div_mul_cancel₀] at *))
    (add safe 0 (by simp only [div_eq_iff] at *))
    (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
    (add safe 0 (by simp only [div_div] at *))
    (add unsafe 50% (by simp only [sq_sub_sq]))
    (add unsafe 50% (by simp only [euler_four_squares]))
    (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
