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


theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by exfalso))
    (add safe 1 (by ring_nf at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero_z]))
    (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero]))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [False.elim]))
    (add norm 0 (by grind only [or_true]))
    (add norm 0 (by grind only [and_self]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [mul_two]))
    (add norm 0 (by grind only [absurd]))
    (add norm 0 (by grind only [true_or]))
    (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
    (add norm 0 (by grind only [Quaternion.star_add_self]))
    (add norm 0 (by grind only [and_true]))
    (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
    (add norm 0 (by grind only [mul_eq_one]))
    (add norm 0 (by grind only [Quaternion.self_add_star]))
    (add norm 0 (by grind only [mul_eq_one_iff]))
    (add norm 0 (by grind only [and_true_iff]))
    (add norm 0 (by grind only [or_not]))
    (add norm 0 (by grind only [EisensteinSeries.r]))
    (add norm 0 (by grind only [or_false]))
    (add norm 0 (by grind only [zero_lt_two']))
    (add unsafe 10% (by grind only [And]))
    (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
    (add unsafe 10% (by grind only [Or.elim]))
    (add unsafe 10% (by grind only [Or]))
    (add unsafe 10% (by grind only [zero_lt_two]))
    (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_lt]))
    (add unsafe 10% (by grind only [Nat.eq_zero_or_pos]))
    (add unsafe 10% (by grind only [SimpleGraph.Walk.IsEulerian.card_filter_odd_degree]))
    (add unsafe 10% (by grind only [mul_lt_mul_left]))
    (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_gt]))
