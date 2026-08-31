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


theorem mathd_algebra_148 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = c * x ^ 3 - 9 * x + 3)
    (h₁ : f 2 = 9) : c = 3 := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 10
    maxNormIterations := 520
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
    (add safe 100 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [sq_eq_sq]))
    (add norm 0 (by grind only [sq_eq_zero_iff]))
    (add norm 0 (by grind only [sq_eq_one_iff]))
    (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [zero_lt_two]))
    (add norm 0 (by grind only [sq_eq_sq_iff_eq_or_eq_neg]))
    (add norm 0 (by grind only [div_eq_one]))
    (add norm 0 (by grind only [Real.sqrt_eq_iff_sq_eq]))
    (add norm 0 (by grind only [sq_pos_of_pos]))
    (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
    (add norm 0 (by grind only [Quaternion.sq_eq_neg_normSq]))
    (add norm 0 (by grind only [mul_eq_one_iff']))
    (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
    (add norm 0 (by grind only [sq_sub_sq]))
    (add norm 0 (by grind only [sq_abs]))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
    (add norm 0 (by grind only [Quaternion.star_eq_self]))
    (add norm 0 (by grind only [legendreSym.eq_zero_mod_of_eq_neg_one]))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [Nat.cast_two]))
    (add norm 0 (by grind only [gaussSum_sq]))
    (add norm 0 (by grind only [sq_nonneg]))
    (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
    (add norm 0 (by grind only [even_two]))
    (add norm 0 (by grind only [Int.sq_of_gcd_eq_one]))
    (add norm 0 (by grind only [CharTwo.two_eq_zero]))
    (add unsafe 90% (by simp only [pow_two] at *))
    (add unsafe 50% (by simp only [sq_add_sq_mul]))
    (add unsafe 90% (by simp only [Real.rpow_two] at *))
    (add unsafe 50% (by nlinarith [div_eq_iff_eq_mul']))
