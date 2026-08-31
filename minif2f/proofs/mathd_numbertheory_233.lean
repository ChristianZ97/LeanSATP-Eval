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


theorem mathd_numbertheory_233 (b : ZMod (11 ^ 2)) (h₀ : b = 24⁻¹) : b = 116 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
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
    (add safe 100 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Char.card_pow_char_pow]))
    (add norm 0 (by grind only [GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible]))
    (add norm 0 (by grind only [Nat.prime_two]))
    (add norm 0 (by grind only [ZMod.sq_add_sq]))
    (add norm 0 (by grind only [gaussSum_sq]))
    (add norm 0 (by grind only [CharP.cast_eq_zero_iff]))
    (add norm 0 (by grind only [ZMod.neg_one_ne_one]))
    (add norm 0 (by grind only [ZMod.eq_zero_iff_even]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [sq_ne_two_fin_zmod_four]))
    (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
    (add norm 0 (by grind only [quadraticChar_eq_pow_of_char_ne_two']))
    (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
    (add norm 0 (by grind only [quadraticChar_eq_one_of_char_two]))
    (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
    (add norm 0 (by grind only [ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime]))
    (add norm 0 (by grind only [MulChar.IsQuadratic]))
    (add norm 0 (by grind only [Int.isUnit_sq]))
    (add norm 0 (by grind only [sq_eq_one_iff]))
    (add unsafe 10% (by grind only [ZMod]))
    (add unsafe 10% (by grind only [FiniteField.two_pow_card]))
    (add unsafe 10% (by grind only [legendreSym.quadratic_reciprocity']))
    (add unsafe 10% (by grind only [Nat.eq_sq_add_sq_of_isSquare_mod_neg_one]))
    (add unsafe 10% (by grind only [mul_left_cancel₀]))
    (add unsafe 10% (by grind only [zero_lt_two]))
    (add unsafe 10% (by grind only [FiniteField.odd_card_of_char_ne_two]))
    (add unsafe 10% (by grind only [ZMod.natCast_zmod_eq_zero_iff_dvd]))
    (add unsafe 10% (by grind only [quadraticChar_neg_one]))
    (add unsafe 10% (by grind only [LucasLehmer.two_lt_q]))
    (add unsafe 10% (by grind only [legendreSym.eq_pow]))
    (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
    (add unsafe 10% (by grind only [mul_right_inj']))
