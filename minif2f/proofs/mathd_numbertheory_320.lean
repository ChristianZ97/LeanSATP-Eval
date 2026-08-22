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


theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by

  aesop (config := {
    maxRuleApplications := 1600
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
    (add safe 100 (by push_neg))
    (add safe 0 (by gcongr))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add unsafe 10% (by grind only [Pell.eq_pell]))
    (add unsafe 10% (by grind only [pow_unbounded_of_one_lt]))
    (add unsafe 10% (by grind only [Nat.sub_lt]))
    (add unsafe 10% (by grind only [Nat.pos_of_dvd_of_pos]))
    (add unsafe 10% (by grind only [PNat.eq_one_of_lt_two]))
    (add unsafe 10% (by grind only [IsPrimePow.one_lt]))
    (add unsafe 10% (by grind only [tsub_pos_of_lt]))
    (add unsafe 10% (by grind only [Nat.eq_zero_of_dvd_of_lt]))
    (add unsafe 10% (by grind only [Nat.le_of_dvd]))
    (add unsafe 10% (by grind only [ascPochhammer_pos]))
    (add unsafe 10% (by grind only [Pell.x_pos]))
    (add unsafe 10% (by grind only [le_of_not_lt]))
    (add unsafe 10% (by grind only [not_lt_of_ge]))
    (add unsafe 10% (by grind only [lt_of_not_ge]))
    (add unsafe 10% (by grind only [lt_of_le_of_ne]))
    (add unsafe 10% (by grind only [Nat.sub_pos_of_lt]))
    (add unsafe 10% (by grind only [Nat.pos_of_ne_zero]))
    (add unsafe 10% (by grind only [pow_eq_zero_of_le]))
    (add unsafe 10% (by grind only [not_le_of_gt]))
    (add unsafe 10% (by grind only [Nat.dist_pos_of_ne]))
    (add unsafe 10% (by grind only [Pell.eq_pow_of_pell_lem]))
    (add unsafe 10% (by grind only [exists_nat_pow_near]))
    (add unsafe 10% (by grind only [Nat.dvd_two_of_totient_le_one]))
    (add unsafe 10% (by grind only [Nat.zero_lt_of_ne_zero]))
    (add unsafe 10% (by grind only [one_lt_mersenne]))
    (add unsafe 10% (by grind only [Nat.not_eq_zero_of_lt]))
    (add unsafe 10% (by grind only [pos_of_gt]))
    (add unsafe 10% (by grind only [Nat.le_sub_one_of_lt]))
    (add unsafe 10% (by grind only [le_of_not_gt]))
    (add unsafe 10% (by grind only [mersenne_pos]))
    (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
    (add unsafe 10% (by grind only [Nat.clog]))
