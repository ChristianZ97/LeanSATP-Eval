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


theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by

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
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by push_neg))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by simp))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Nat.sub_add_cancel]))
    (add norm 0 (by grind only [Nat.add_sub_of_le]))
    (add norm 0 (by grind only [tsub_add_cancel_of_le]))
    (add norm 0 (by grind only [sub_eq_add]))
    (add norm 0 (by grind only [add_tsub_cancel_of_le]))
    (add norm 0 (by grind only [tsub_tsub_cancel_of_le]))
    (add norm 0 (by grind only [Nat.sub_sub_self]))
    (add norm 0 (by grind only [Nat.cast_sub]))
    (add norm 0 (by grind only [eq_tsub_of_add_eq]))
    (add norm 0 (by grind only [div_eq_iff_eq_mul]))
    (add norm 0 (by grind only [Nat.sub_add_comm]))
    (add norm 0 (by grind only [Nat.sub_eq_zero_of_le]))
    (add norm 0 (by grind only [Nat.add_sub_cancel']))
    (add norm 0 (by grind only [Nat.add_sub_assoc]))
    (add norm 0 (by grind only [eq_div_iff_mul_eq']))
    (add norm 0 (by grind only [div_eq_iff_eq_mul']))
    (add norm 0 (by grind only [Nat.psub_eq_sub]))
    (add norm 0 (by grind only [eq_tsub_iff_add_eq_of_le]))
    (add norm 0 (by grind only [tsub_eq_iff_eq_add_of_le]))
    (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
    (add norm 0 (by grind only [Nat.cast_tsub]))
    (add norm 0 (by grind only [Nat.even_sub]))
    (add norm 0 (by grind only [Nat.dvd_sub]))
    (add norm 0 (by grind only [add_tsub_cancel_left]))
    (add unsafe 10% (by grind only [Nat.modEq_iff_dvd']))
    (add unsafe 10% (by grind only [Nat.sub_le]))
    (add unsafe 10% (by grind only [Nat.le_sub_one_of_lt]))
    (add unsafe 10% (by grind only [le_tsub_of_add_le_left]))
    (add unsafe 10% (by grind only [Int.ofNat_sub]))
    (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
    (add unsafe 10% (by grind only [Nat.exists_eq_add_of_le]))
    (add unsafe 10% (by grind only [Nat.mod_lt]))
