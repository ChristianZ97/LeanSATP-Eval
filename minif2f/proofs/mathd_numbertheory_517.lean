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


theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    maxGoals := 16
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by simp))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by ext))
    (add safe 0 (by split))
    (add safe 1 (by ring_nf at *))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Nat.mod_two_add_succ_mod_two]))
    (add unsafe 50% (by nlinarith [Nat.mul_mod_left]))
    (add unsafe 50% (by nlinarith [Nat.mul_mod]))
    (add unsafe 50% (by nlinarith [Int.emod_two_ne_one]))
    (add unsafe 50% (by nlinarith [Nat.mod_two_ne_zero]))
    (add unsafe 50% (by nlinarith [Nat.mod_two_ne_one]))
    (add unsafe 50% (by nlinarith [Nat.mul_mod_mul_left]))
    (add unsafe 50% (by nlinarith [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 50% (by nlinarith [Nat.mul_mod_right]))
    (add unsafe 50% (by nlinarith [Int.mul_emod]))
    (add unsafe 50% (by nlinarith [Nat.even_iff]))
    (add unsafe 50% (by nlinarith [Nat.mul_mod_mod]))
    (add unsafe 50% (by nlinarith [Int.emod_two_ne_zero]))
    (add unsafe 50% (by nlinarith [Int.emod_two_eq_zero_or_one]))
    (add unsafe 50% (by nlinarith [Nat.odd_iff]))
    (add unsafe 50% (by nlinarith [Int.odd_iff]))
    (add unsafe 50% (by nlinarith [Int.sq_ne_two_mod_four]))
    (add unsafe 50% (by nlinarith [Nat.gcd.induction]))
    (add unsafe 50% (by nlinarith [Int.add_emod]))
    (add unsafe 50% (by nlinarith [Nat.mod_mul_left_mod]))
    (add unsafe 50% (by nlinarith [Nat.mod_two_of_bodd]))
    (add unsafe 50% (by nlinarith [Int.even_iff]))
    (add unsafe 50% (by nlinarith [coprime_sq_sub_sq_sum_of_odd_odd]))
    (add unsafe 50% (by nlinarith [neg_one_pow_eq_pow_mod_two]))
    (add unsafe 50% (by nlinarith [Nat.pow_mod]))
    (add unsafe 50% (by nlinarith [Nat.not_even_iff]))
    (add unsafe 50% (by nlinarith [ZMod.χ₈_nat_eq_if_mod_eight]))
    (add unsafe 50% (by nlinarith [Nat.mod_mod]))
    (add unsafe 50% (by nlinarith [Int.neg_emod_two]))
    (add unsafe 50% (by nlinarith [Nat.mod_mod_of_dvd]))
    (add unsafe 50% (by nlinarith [Int.mul_emod_right]))
    (add unsafe 50% (by nlinarith [Int.emod_eq_emod_iff_emod_sub_eq_zero]))
