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


theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by

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
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 0 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by exfalso))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [sq_pos_of_pos]))
    (add norm 0 (by grind only [Real.sqrt_pos]))
    (add norm 0 (by grind only [zero_lt_two']))
    (add norm 0 (by grind only [zero_lt_two]))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [mul_self_pos]))
    (add norm 0 (by grind only [Real.rpow_pos_of_pos]))
    (add norm 0 (by grind only [mul_nonneg_iff_of_pos_left]))
    (add norm 0 (by grind only [EisensteinSeries.r1]))
    (add norm 0 (by grind only [Real.log_rpow]))
    (add norm 0 (by grind only [one_half_pos]))
    (add norm 0 (by grind only [two_ne_zero']))
    (add norm 0 (by grind only [Hyperreal.coe_pos]))
    (add norm 0 (by grind only [bernsteinApproximation.δ_pos]))
    (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half_of_pos]))
    (add norm 0 (by grind only [Real.cosh_pos]))
    (add norm 0 (by grind only [Real.exp_half]))
    (add safe 0 (by simp only [mul_div_cancel₀] at *))
    (add safe 0 (by nlinarith [Real.pi_pos]))
    (add safe 0 (by nlinarith [Real.pi_div_two_pos]))
    (add safe 0 (by simp only [div_mul_cancel₀] at *))
    (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
    (add unsafe 50% (by nlinarith [Real.mul_pos]))
    (add unsafe 50% (by nlinarith [Real.aux₀]))
    (add unsafe 50% (by nlinarith [div_lt_iff]))
    (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_right]))
    (add unsafe 50% (by nlinarith [EisensteinSeries.r1_pos]))
    (add unsafe 50% (by nlinarith [div_lt_iff']))
    (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
    (add unsafe 50% (by nlinarith [one_lt_div]))
