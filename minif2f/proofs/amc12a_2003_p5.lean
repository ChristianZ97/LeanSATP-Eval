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


theorem amc12a_2003_p5 (A M C : ℕ) (h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
    (h₁ : Nat.ofDigits 10 [0, 1, C, M, A] + Nat.ofDigits 10 [2, 1, C, M, A] = 123422) :
    A + M + C = 14 := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableSimp := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 100 (by exfalso))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by interval_cases))
    (add safe 0 (by ext))
    (add safe 0 (by split))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Nat.ofDigits_one]))
    (add norm 0 (by grind only [Nat.ofDigits]))
    (add norm 0 (by grind only [Nat.ofDigits_digits]))
    (add norm 0 (by grind only [Nat.ofDigits_singleton]))
    (add norm 0 (by grind only [Nat.digits_ofDigits]))
    (add norm 0 (by grind only [Nat.ofDigits_monotone]))
    (add norm 0 (by grind only [Nat.sum_le_ofDigits]))
    (add norm 0 (by grind only [add_self]))
    (add norm 0 (by grind only [Nat.ofDigits_cons]))
    (add norm 0 (by grind only [Nat.self_div_pow_eq_ofDigits_drop]))
    (add norm 0 (by grind only [Nat.ofDigits_mod_eq_head!]))
    (add norm 0 (by grind only [Nat.ofDigits_div_pow_eq_ofDigits_drop]))
    (add norm 0 (by rw [mul_self]))
    (add norm 0 (by grind only [Nat.ofDigits_modEq]))
    (add norm 0 (by rw [mul_one]))
    (add norm 0 (by rw [one_mul]))
    (add norm 0 (by rw [mul_le_mul_iff_left]))
    (add norm 0 (by grind only [Nat.mod_add_div]))
    (add norm 0 (by grind only [Nat.div_add_mod]))
    (add norm 0 (by grind only [Nat.add_eq]))
    (add norm 0 (by grind only [Nat.one_add]))
    (add norm 0 (by grind only [Stream'.Seq.drop]))
    (add norm 0 (by grind only [Stream'.WSeq.dropn_add]))
    (add norm 0 (by grind only [Hindman.FP.mul]))
    (add norm 0 (by grind only [Hindman.FP_drop_subset_FP]))
    (add norm 0 (by grind only [Stream'.drop_drop]))
    (add norm 0 (by grind only [Nat.ofDigits_div_eq_ofDigits_tail]))
    (add norm 0 (by grind only [Stream'.WSeq.dropn_ofSeq]))
    (add norm 0 (by grind only [Stream'.WSeq.dropn_cons]))
    (add norm 0 (by grind only [Stream'.Seq.dropn_add]))
    (add norm 0 (by grind only [Ordnode.drop]))
    (add unsafe 50% (by nlinarith [Nat.ofDigits_zmodeq]))
