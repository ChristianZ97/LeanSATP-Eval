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


theorem mathd_numbertheory_447 :
    ∑ k ∈ Finset.filter (fun x => 3 ∣ x) (Finset.Icc 1 49), k % 10 = 78 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 380
    maxNormIterations := 320
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by bound))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by omega))
    (add safe 100 (by push_neg))
    (add safe 100 (by ring_nf))
    (add safe 0 (by split))
    (add safe 100 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Finset.Icc]))
    (add norm 0 (by grind only [Nat.Ico_zero_eq_range]))
    (add norm 0 (by grind only [Nat.card_Icc]))
    (add norm 0 (by grind only [Pi.card_Icc]))
    (add norm 0 (by grind only [Nat.prod_Icc_factorial]))
    (add norm 0 (by rw [Int.card_Icc]))
    (add norm 0 (by grind only [Finset.range_eq_Ico]))
    (add norm 0 (by grind only [primorial]))
    (add norm 0 (by grind only [Finset.Icc_self]))
    (add norm 0 (by grind only [Finset.card_range]))
    (add norm 0 (by grind only [PNat.card_Icc]))
    (add norm 0 (by grind only [Finset.prod_Ico_consecutive]))
    (add norm 0 (by grind only [Finset.Icc_eq_cons_Ico]))
    (add norm 0 (by grind only [Finset.prod_Ico_add]))
    (add norm 0 (by grind only [Finset.prod_Ico_add']))
    (add norm 0 (by grind only [Finset.prod_range_mul_prod_Ico]))
    (add norm 0 (by grind only [Nat.Prime.multiplicity_choose_aux]))
    (add norm 0 (by grind only [Fin.card_Icc]))
    (add norm 0 (by grind only [eVariationOn.sum_le_of_monotoneOn_Icc]))
    (add norm 0 (by grind only [Finset.Ico_self]))
    (add norm 0 (by grind only [Finset.Ico_insert_right]))
    (add norm 0 (by grind only [Nat.cast_sum]))
    (add norm 0 (by grind only [Finset.prod_empty]))
    (add safe 0 (by field_simp [Finset.prod_singleton] at *))
    (add unsafe 10% (by field_simp [harmonic_eq_sum_Icc] at *))
    (add unsafe 10% (by field_simp [Finset.Icc_eq_empty_of_lt] at *))
    (add unsafe 10% (by field_simp [PicardLindelof.proj_coe] at *))
    (add unsafe 10% (by field_simp [Finset.Icc_neg_mono] at *))
    (add unsafe 10% (by field_simp [Finset.prod_Icc_succ_top] at *))
    (add unsafe 10% (by field_simp [Fin.Icc_eq_finset_subtype] at *))
    (add unsafe 10% (by field_simp [MonotoneOn.sum_le_integral_Ico] at *))
    (add unsafe 10% (by field_simp [Set.projIcc_of_mem] at *))
