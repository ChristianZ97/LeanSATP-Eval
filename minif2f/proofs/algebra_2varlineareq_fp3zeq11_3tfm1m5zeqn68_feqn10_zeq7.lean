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


theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 (f z : ℂ) (h₀ : f + 3 * z = 11)
    (h₁ : 3 * (f - 1) - 5 * z = -68) : f = -10 ∧ z = 7 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 600
    maxNormIterations := 320
    maxGoals := 512
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
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by exfalso))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 90% (by positivity))
    (add norm 0 (by grind only [Complex.two_pi_I_ne_zero]))
    (add norm 0 (by grind only [Complex.I_ne_zero]))
    (add norm 0 (by grind only [Complex.I]))
    (add norm 0 (by grind only [Complex.arctan]))
    (add norm 0 (by grind only [neg_div]))
    (add norm 0 (by grind only [Complex.sin]))
    (add norm 0 (by grind only [Complex.cpow_neg_one]))
    (add norm 0 (by grind only [Complex.I_sq]))
    (add norm 0 (by grind only [HurwitzZeta.sinZeta]))
    (add norm 0 (by grind only [Complex.Gammaℂ]))
    (add norm 0 (by grind only [Real.pi_ne_zero]))
    (add norm 0 (by grind only [Complex.exp_ne_zero]))
    (add norm 0 (by grind only [two_ne_zero']))
    (add norm 0 (by grind only [Complex.exp]))
    (add norm 0 (by grind only [Complex.ofReal_cpow_of_nonpos]))
    (add norm 0 (by grind only [Complex.div_I]))
    (add norm 0 (by grind only [jacobiTheta₂]))
    (add norm 0 (by grind only [jacobiTheta]))
    (add norm 0 (by grind only [Complex.exp_sub]))
    (add norm 0 (by grind only [quadratic_eq_zero_iff]))
    (add norm 0 (by grind only [Complex.exp_log]))
    (add norm 0 (by grind only [div_eq_mul_inv]))
    (add norm 0 (by grind only [jacobiTheta₂_functional_equation]))
    (add safe 0 (by nlinarith [Real.two_pi_pos]))
    (add safe 0 (by simp only [mul_div_assoc] at *))
    (add safe 0 (by simp only [div_eq_iff] at *))
    (add safe 0 (by nlinarith [Real.pi_pos]))
    (add unsafe 50% (by nlinarith [mul_neg_one]))
    (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
    (add unsafe 50% (by nlinarith [Real.arctan_ne_mul_pi_div_two]))
    (add unsafe 50% (by nlinarith [Complex.I_mul_I]))
    (add unsafe 50% (by nlinarith [div_eq_iff_eq_mul]))
