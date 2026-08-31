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


theorem mathd_numbertheory_12 :
    Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    })
    (add norm 0 (by ring))
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by bound))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by omega))
    (add safe 100 (by push_neg))
    (add safe 0 (by split))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Nat.card_Icc]))
    (add norm 0 (by grind only [PNat.card_Icc]))
    (add norm 0 (by grind only [Fin.card_Icc]))
    (add norm 0 (by grind only [Pi.card_Icc]))
    (add norm 0 (by grind only [Int.card_Icc]))
    (add norm 0 (by grind only [Finset.card_singleton]))
    (add norm 0 (by grind only [Int.card_Icc_of_le]))
    (add norm 0 (by grind only [Multiset.card_Icc]))
    (add norm 0 (by grind only [Sigma.card_Icc]))
    (add norm 0 (by grind only [Finset.card_one]))
    (add norm 0 (by grind only [Finset.card_Icc_finset]))
    (add norm 0 (by grind only [Finsupp.card_Icc]))
    (add norm 0 (by grind only [Prod.card_Icc]))
    (add norm 0 (by grind only [Finset.Icc]))
    (add norm 0 (by grind only [Finset.card_eq_sum_ones]))
    (add norm 0 (by grind only [Finset.card_Ico_eq_card_Icc_sub_one]))
    (add norm 0 (by grind only [DFinsupp.card_Icc]))
    (add norm 0 (by grind only [Finset.cast_card]))
    (add norm 0 (by grind only [Int.card_fintype_Icc]))
    (add norm 0 (by grind only [Nat.card_fintypeIcc]))
    (add norm 0 (by grind only [SimpleGraph.dart_card_eq_twice_card_edges]))
    (add norm 0 (by grind only [Finset.card]))
    (add norm 0 (by grind only [Finset.sum_const_nat]))
    (add norm 0 (by grind only [Finset.card_pair]))
    (add norm 0 (by grind only [Finset.card_powerset]))
    (add norm 0 (by grind only [Finset.card_powersetCard]))
    (add norm 0 (by grind only [Nat.card_Ico]))
    (add norm 0 (by grind only [Finset.card_map]))
    (add norm 0 (by grind only [Fin.card_Ioi]))
    (add norm 0 (by grind only [Set.toFinset_Icc]))
    (add norm 0 (by grind only [Finset.card_singleton_mul]))
    (add unsafe 10% (by field_simp [PNat.card_fintype_Icc] at *))
