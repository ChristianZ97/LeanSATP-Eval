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


theorem mathd_algebra_171 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 4) : f 1 = 9 := by

  aesop (config := {
    maxRuleApplications := 40
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
    (add safe 0 (by split))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Real.exp_zero]))
    (add norm 0 (by grind only [mul_one]))
    (add norm 0 (by grind only [one_mul]))
    (add norm 0 (by grind only [Pi.one_apply]))
    (add norm 0 (by grind only [div_one]))
    (add norm 0 (by grind only [one_ne_zero]))
    (add norm 0 (by grind only [ProbabilityTheory.mgf]))
    (add norm 0 (by grind only [abs_one]))
    (add norm 0 (by grind only [integral_one]))
    (add norm 0 (by grind only [MeasureTheory.hausdorffMeasure_real]))
    (add norm 0 (by grind only [Real.exp_eq_one_iff]))
    (add norm 0 (by grind only [Real.rpow_zero]))
    (add norm 0 (by grind only [Real.one_rpow]))
    (add norm 0 (by grind only [ContinuousMap.one_apply]))
    (add norm 0 (by grind only [Real.log_one]))
    (add norm 0 (by grind only [Real.Gamma_one]))
    (add norm 0 (by grind only [Real.exp_eq_exp]))
    (add norm 0 (by grind only [sq_eq_one_iff]))
    (add norm 0 (by grind only [TrivSqZeroExt.inl_one]))
    (add norm 0 (by grind only [IsLprojection.coe_compl]))
    (add norm 0 (by grind only [ProbabilityTheory.mgf_zero']))
    (add norm 0 (by grind only [ENNReal.one_toReal]))
    (add norm 0 (by grind only [ContinuousMap.coe_one]))
    (add norm 0 (by grind only [mul_eq_one]))
    (add norm 0 (by grind only [MeasureTheory.lintegral_one]))
    (add norm 0 (by grind only [NNReal.coe_one]))
    (add norm 0 (by grind only [mabs_one]))
    (add norm 0 (by grind only [mul_eq_one_iff']))
    (add norm 0 (by grind only [ProbabilityTheory.mgf_zero]))
    (add norm 0 (by grind only [LSeries.term_delta]))
    (add norm 0 (by grind only [ENNReal.ofReal_one]))
    (add norm 0 (by grind only [ENNReal.log_one]))
