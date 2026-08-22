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


theorem mathd_algebra_478 (b h v : ℝ) (h₀ : 0 < b ∧ 0 < h ∧ 0 < v) (h₁ : v = 1 / 3 * (b * h))
    (h₂ : b = 30) (h₃ : h = 13 / 2) : v = 65 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    maxGoals := 256
    enableSimp := false
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 1 (by push_neg))
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
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add norm 0 (by grind only [one_div]))
    (add norm 0 (by grind only [Real.rpow_mul]))
    (add safe 0 (by nlinarith [Real.pi_pos]))
    (add safe 1 (by unfold div_le_iff'))
    (add safe 100 (by simp only [mul_div_cancel₀] at *))
    (add safe 1 (by unfold div_le_iff))
    (add safe 1 (by unfold le_div_iff))
    (add unsafe 50% (by nlinarith [Real.rpow_pos_of_pos]))
    (add unsafe 50% (by nlinarith [mul_le_mul_right]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
    (add unsafe 50% (by nlinarith [le_div_iff']))
    (add unsafe 50% (by nlinarith [mul_le_mul_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
    (add unsafe 10% (by grind only [ne_of_gt]))
    (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
    (add unsafe 50% (by nlinarith [div_lt_iff]))
    (add unsafe 50% (by nlinarith [EisensteinSeries.r1_pos]))
    (add unsafe 50% (by nlinarith [Real.log_rpow]))
    (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
    (add unsafe 50% (by nlinarith [one_half_pos]))
    (add unsafe 50% (by nlinarith [div_lt_iff']))
    (add unsafe 50% (by nlinarith [mul_nonneg_iff_of_pos_right]))
    (add unsafe 50% (by nlinarith [one_lt_div]))
    (add unsafe 50% (by nlinarith [Real.sqrt_pos]))
    (add unsafe 50% (by nlinarith [Real.b_pos]))
    (add unsafe 10% (by grind only [Real.rpow_one]))
    (add unsafe 50% (by nlinarith [Real.pi_div_two_pos]))
    (add unsafe 50% (by nlinarith [bernsteinApproximation.δ_pos]))
    (add unsafe 50% (by nlinarith [inv_pos]))
    (add unsafe 50% (by nlinarith [lt_div_iff]))
    (add unsafe 50% (by nlinarith [Real.aux₀]))
    (add unsafe 50% (by nlinarith [zero_lt_two]))
