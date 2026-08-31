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


theorem mathd_algebra_304 : 91 ^ 2 = 8281 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableSimp := false
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 50% (by ring_nf at *))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
    (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
    (add norm 0 (by grind only [quadraticChar_sq_one]))
    (add norm 0 (by grind only [quadraticChar_sq_one']))
    (add norm 0 (by grind only [neg_one_sq]))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
    (add norm 0 (by grind only [legendreSym.sq_one]))
    (add norm 0 (by grind only [mul_pow]))
    (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
    (add norm 0 (by grind only [euler_four_squares]))
    (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
    (add norm 0 (by grind only [sq_add_sq_mul]))
    (add norm 0 (by grind only [qrSign.sq_eq_one]))
    (add norm 0 (by grind only [sq_sub_sq]))
    (add norm 0 (by grind only [legendreSym.sq_one']))
    (add norm 0 (by grind only [Int.isUnit_sq]))
    (add norm 0 (by grind only [one_pow]))
    (add norm 0 (by grind only [even_two]))
    (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
    (add norm 0 (by grind only [pow_mul]))
    (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
    (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
    (add norm 0 (by grind only [Int.cast_ofNat]))
    (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
    (add norm 0 (by grind only [Pell.Solution₁.prop]))
    (add norm 0 (by grind only [gaussSum_sq]))
    (add norm 0 (by grind only [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq]))
    (add norm 0 (by grind only [pow_two_pow_sub_pow_two_pow]))
    (add norm 0 (by grind only [neg_sq]))
    (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
    (add unsafe 90% (by simp only [pow_two] at *))
    (add unsafe 90% (by simp only [Real.rpow_two] at *))
