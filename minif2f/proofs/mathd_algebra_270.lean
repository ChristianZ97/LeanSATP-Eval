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


theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 600
    maxNormIterations := 320
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
    (add safe 100 (by omega))
    (add safe 100 (by push_neg))
    (add safe 100 (by interval_cases))
    (add safe 0 (by ext))
    (add safe 0 (by split))
    (add safe 0 (by exfalso))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 90% (by norm_num [*] at *))
    (add norm 0 (by grind only [one_div]))
    (add norm 0 (by grind only [neg_div]))
    (add norm 0 (by grind only [div_eq_mul_inv]))
    (add norm 0 (by grind only [inv_div]))
    (add norm 0 (by grind only [div_eq_inv_mul]))
    (add norm 0 (by grind only [div_neg]))
    (add norm 0 (by grind only [two_ne_zero']))
    (add norm 0 (by grind only [div_one]))
    (add norm 0 (by grind only [div_inv_eq_mul]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [mul_inv]))
    (add norm 0 (by grind only [Complex.ofReal_inv]))
    (add norm 0 (by grind only [one_ne_zero]))
    (add norm 0 (by grind only [LSeries.term_of_ne_zero]))
    (add norm 0 (by grind only [mul_one_div]))
    (add norm 0 (by grind only [neg_eq]))
    (add norm 0 (by grind only [sub_half]))
    (add norm 0 (by grind only [mul_div_cancel_left]))
    (add norm 0 (by grind only [div_self']))
    (add norm 0 (by grind only [harmonic_succ]))
    (add norm 0 (by grind only [Real.arctan]))
    (add norm 0 (by grind only [Complex.arctan]))
    (add safe 0 (by simp only [div_self] at *))
    (add safe 0 (by simp only [sub_div] at *))
    (add safe 0 (by simp only [eq_div_iff] at *))
    (add safe 0 (by simp only [div_div] at *))
    (add safe 0 (by simp only [mul_div_assoc] at *))
    (add safe 0 (by simp only [Complex.Gammaℝ] at *))
    (add safe 0 (by simp only [div_eq_iff] at *))
    (add safe 0 (by simp only [HurwitzZeta.hurwitzZetaEven] at *))
    (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
    (add safe 0 (by simp only [div_ne_one] at *))
