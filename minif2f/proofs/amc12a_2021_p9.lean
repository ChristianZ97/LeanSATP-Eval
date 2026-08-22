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


theorem amc12a_2021_p9 : ∏ k ∈ Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k) = 3 ^ 128 - 2 ^ 128 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 380
    maxNormIterations := 320
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
    (add norm 1 (by simp))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by omega))
    (add safe 100 (by push_neg))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by exfalso))
    (add safe 100 (by simp_all))
    (add safe 100 (by ring_nf at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Finset.prod_range_succ]))
    (add norm 0 (by grind only [Finset.prod_range_succ']))
    (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
    (add norm 0 (by grind only [Nat.choose_self]))
    (add norm 0 (by grind only [Finset.prod_range_zero]))
    (add norm 0 (by grind only [tsub_zero]))
    (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
    (add norm 0 (by grind only [Finset.prod_range_one]))
    (add norm 0 (by grind only [Finset.prod_range]))
    (add norm 0 (by grind only [Finset.range_succ]))
    (add norm 0 (by grind only [Finset.card_range]))
    (add norm 0 (by grind only [geom_sum₂_with_one]))
    (add norm 0 (by grind only [add_pow]))
    (add norm 0 (by grind only [Nat.choose_zero_right]))
    (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
    (add norm 0 (by grind only [sum_bernoulli]))
    (add norm 0 (by grind only [geom_sum_mul_add]))
    (add norm 0 (by grind only [Finset.range_add_one]))
    (add norm 0 (by grind only [Finset.range_zero]))
    (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
    (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
    (add norm 0 (by grind only [Nat.choose_one_right]))
    (add norm 0 (by grind only [Nat.factorial]))
    (add norm 0 (by grind only [tsub_self]))
    (add norm 0 (by grind only [bernsteinPolynomial.sum]))
    (add norm 0 (by grind only [Nat.choose_succ_self_right]))
    (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
    (add norm 0 (by grind only [pow_one]))
    (add norm 0 (by grind only [sum_range_pow]))
    (add norm 0 (by grind only [wittPolynomial_eq_sum_C_mul_X_pow]))
    (add norm 0 (by grind only [mul_geom_sum]))
    (add safe 0 (by simp only [Finset.range_one] at *))
