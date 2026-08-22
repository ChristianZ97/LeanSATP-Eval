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


theorem mathd_algebra_76 (f : ℤ → ℤ) (h₀ : ∀ n, Odd n → f n = n ^ 2)
    (h₁ : ∀ n, Even n → f n = n ^ 2 - 4 * n - 1) : f 4 = -1 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 520
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by simp))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 90% (by positivity))
    (add norm 0 (by grind only [Odd]))
    (add norm 0 (by grind only [IsSquare]))
    (add norm 0 (by grind only [ZMod.eq_zero_iff_even]))
    (add norm 0 (by grind only [Int.even_coe_nat]))
    (add safe 0 (by simp_all [Int.cast_inj]))
    (add unsafe 10% (by grind only [even_iff_two_dvd]))
    (add unsafe 50% (by rw [← Int.natCast_inj] at *))
    (add unsafe 50% (by nlinarith [Int.odd_iff_not_even]))
    (add unsafe 10% (by grind only [jacobiSym.at_two]))
    (add unsafe 50% (by nlinarith [Nat.even_or_odd]))
    (add unsafe 50% (by nlinarith [Nat.odd_iff_not_even]))
    (add unsafe 10% (by grind only [irrational_sqrt_of_multiplicity_odd]))
    (add unsafe 50% (by nlinarith [Int.emod_eq_zero_of_dvd]))
    (add unsafe 50% (by nlinarith [Int.even_iff]))
    (add unsafe 50% (by nlinarith [Nat.odd_iff]))
    (add unsafe 50% (by nlinarith [Int.even_pow]))
    (add unsafe 10% (by grind only [Int.even_mul]))
    (add unsafe 50% (by nlinarith [Nat.even_iff]))
    (add unsafe 50% (by nlinarith [Int.dvd_iff_emod_eq_zero]))
    (add unsafe 50% (by nlinarith [Nat.even_pow]))
    (add unsafe 50% (by nlinarith [Nat.even_mul]))
    (add unsafe 10% (by grind only [FiniteField.odd_card_of_char_ne_two]))
    (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
    (add unsafe 50% (by nlinarith [Nat.odd_of_mod_four_eq_three]))
    (add unsafe 50% (by rw [← Int.ofNat_inj] at *))
    (add unsafe 50% (by nlinarith [jacobiSym.quadratic_reciprocity_three_mod_four]))
    (add unsafe 50% (by nlinarith [Int.even_iff_not_odd]))
    (add unsafe 50% (by nlinarith [Int.odd_iff]))
    (add unsafe 50% (by nlinarith [Nat.not_even_iff]))
    (add unsafe 50% (by nlinarith [Int.emod_two_eq_zero_or_one]))
    (add unsafe 50% (by nlinarith [Fermat42.not_minimal]))
    (add unsafe 50% (by nlinarith [jacobiSym.quadratic_reciprocity_one_mod_four]))
