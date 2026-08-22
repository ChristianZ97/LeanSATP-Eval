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


theorem mathd_algebra_432 (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 600
    maxNormIterations := 320
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
    (add safe 100 (by positivity))
    (add safe 0 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by exfalso))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [two_ne_zero']))
    (add norm 0 (by grind only [Real.Gamma_two]))
    (add norm 0 (by grind only [zero_lt_two]))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [mul_two]))
    (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
    (add norm 0 (by grind only [zero_lt_two']))
    (add norm 0 (by grind only [Nat.cast_two]))
    (add norm 0 (by grind only [Quaternion.star_add_self]))
    (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half_of_pos]))
    (add norm 0 (by grind only [Quaternion.self_add_star]))
    (add norm 0 (by grind only [Real.Gamma_add_one]))
    (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half]))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [integral_id]))
    (add norm 0 (by grind only [Real.doublingGamma]))
    (add norm 0 (by grind only [even_two]))
    (add norm 0 (by grind only [sq_pos_of_pos]))
    (add norm 0 (by grind only [CircleDeg1Lift.transnumAuxSeq]))
    (add norm 0 (by grind only [Nat.factorial_two]))
    (add norm 0 (by grind only [Real.cos_sq]))
    (add safe 0 (by simp only [mul_div_assoc] at *))
    (add safe 0 (by simp only [mul_div_cancel₀] at *))
    (add safe 0 (by simp only [mul_div] at *))
    (add safe 0 (by simp only [div_div] at *))
    (add safe 0 (by simp only [div_self] at *))
    (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
    (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
    (add safe 0 (by simp only [div_mul] at *))
    (add safe 0 (by simp only [sub_div] at *))
    (add unsafe 50% (by simp only [sq_sub_sq]))
