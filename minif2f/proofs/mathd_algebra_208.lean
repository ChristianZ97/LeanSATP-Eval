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


theorem mathd_algebra_208 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 100 (by ring_nf))
    (add norm 1 (by simp))
    (add norm 1 (by field_simp [*] at *))
    (add norm 1 (by norm_num [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 0 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Real.sqrt_pos]))
    (add norm 0 (by grind only [Real.div_sqrt]))
    (add norm 0 (by grind only [Real.sqrt_one]))
    (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [Real.sqrt_sq]))
    (add norm 0 (by grind only [Stirling.stirlingSeq]))
    (add norm 0 (by grind only [Real.sqrt_inv]))
    (add norm 0 (by grind only [Real.hasDerivAt_sqrt]))
    (add norm 0 (by grind only [Real.sqrt_div]))
    (add norm 0 (by grind only [Real.mul_self_sqrt]))
    (add norm 0 (by grind only [Real.sqrt_mul_self]))
    (add norm 0 (by grind only [Real.deriv_arccos]))
    (add norm 0 (by grind only [integral_gaussian]))
    (add norm 0 (by grind only [Real.cos_pi_over_two_pow]))
    (add norm 0 (by grind only [Real.cos_half]))
    (add norm 0 (by grind only [Real.sqrt_mul]))
    (add norm 0 (by grind only [Real.log_div]))
    (add norm 0 (by grind only [Real.sqrt_mul']))
    (add norm 0 (by grind only [Real.Gamma_pos_of_pos]))
    (add norm 0 (by grind only [Real.doublingGamma]))
    (add norm 0 (by grind only [Real.rpow_div_two_eq_sqrt]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [Real.sin_sq_pi_over_two_pow_succ]))
    (add norm 0 (by grind only [Real.exp_half]))
    (add norm 0 (by grind only [Real.sqrt_nonneg]))
    (add norm 0 (by grind only [Real.sqrt]))
    (add norm 0 (by grind only [Real.sqrt_zero]))
    (add norm 0 (by grind only [Real.inv_sqrt_one_add_tan_sq]))
    (add norm 0 (by grind only [Real.sin_pi_over_two_pow_succ]))
    (add safe 0 (by linarith [zero_lt_two]))
    (add safe 100 (by simp_all [Real.cos_arctan]))
