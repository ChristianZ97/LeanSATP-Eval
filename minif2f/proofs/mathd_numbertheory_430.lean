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


theorem mathd_numbertheory_430 (a b c : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 1 ≤ b ∧ b ≤ 9)
    (h₂ : 1 ≤ c ∧ c ≤ 9) (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c) (h₆ : a + b = c)
    (h₇ : 10 * a + a - b = 2 * c) (h₈ : c * b = 10 * a + a + a) : a + b + c = 8 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    maxGoals := 256
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 100 (by exfalso))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Nat.add_sub_of_le]))
    (add norm 0 (by grind only [mul_comm]))
    (add norm 0 (by grind only [add_tsub_cancel_of_le]))
    (add norm 0 (by grind only [tsub_add_cancel_of_le]))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
    (add norm 0 (by grind only [Eq.symm]))
    (add norm 0 (by grind only [mul_left_comm]))
    (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
    (add norm 0 (by grind only [Nat.add_sub_cancel']))
    (add norm 0 (by grind only [Nat.add_sub_assoc]))
    (add norm 0 (by grind only [add_tsub_assoc_of_le]))
    (add norm 0 (by grind only [tsub_add_eq_add_tsub]))
    (add norm 0 (by grind only [add_tsub_cancel_left]))
    (add norm 0 (by grind only [Finset.mulETransformRight.card]))
    (add norm 0 (by grind only [mul_two]))
    (add norm 0 (by grind only [mul_assoc]))
    (add norm 0 (by grind only [Nat.sub_add_cancel]))
    (add norm 0 (by grind only [tsub_add_tsub_cancel]))
    (add norm 0 (by grind only [mul_right_comm]))
    (add norm 0 (by grind only [mul_tsub]))
    (add norm 0 (by grind only [add_tsub_cancel_right]))
    (add norm 0 (by grind only [eq_tsub_of_add_eq]))
    (add norm 0 (by grind only [ack_two]))
    (add norm 0 (by grind only [Nat.div_add_mod]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [Sym2.two_mul_card_image_offDiag]))
    (add norm 0 (by grind only [Eq.trans]))
    (add norm 0 (by grind only [Nat.add_sub_cancel]))
    (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
    (add norm 0 (by grind only [sub_eq_add]))
    (add norm 0 (by grind only [Nat.add_sub_cancel_left]))
