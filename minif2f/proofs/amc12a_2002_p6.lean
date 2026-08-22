
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


set_option maxHeartbeats 0

theorem amc12a_2002_p6 (n : ℕ) (h₀ : 0 < n) : ∃ m, m > n ∧ ∃ p, m * p ≤ m + p := by
  -- Step 9: Let m = n + 1
  let m := n + 1

  -- Step 10: Show m > n
  have h_step10 : m > n := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.succ_sub]))
      (add norm 0 (by grind only [Nat.succ_pos']))
      (add norm 0 (by grind only [ack_zero]))
      (add norm 0 (by grind only [Nat.succ_eq_add_one]))
      (add norm 0 (by grind only [Nat]))
      (add unsafe 10% (by grind only [Nat.succ_pos]))
      (add unsafe 10% (by grind only [Nat.le_of_lt_succ]))
      (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
      (add unsafe 10% (by grind only [Nat.le_succ]))
      (add unsafe 10% (by grind only [Nat.zero_lt_succ]))
      (add unsafe 10% (by grind only [Nat.succ_le_succ]))
      (add unsafe 10% (by grind only [Nat.lt_succ_self]))
      (add unsafe 10% (by grind only [Nat.lt_of_succ_le]))
      (add unsafe 10% (by grind only [Nat.succ_lt_succ]))
      (add unsafe 10% (by grind only [Nat.lt_succ_of_le]))
      (add unsafe 10% (by grind only [Nat.succ_le_iff]))
      (add unsafe 10% (by grind only [Nat.lt_succ]))
      (add unsafe 10% (by grind only [Nat.succ_le]))
      (add unsafe 10% (by grind only [Nat.le_of_succ_le_succ]))
      (add unsafe 10% (by grind only [Nat.lt_succ_iff]))
      (add unsafe 10% (by grind only [Nat.lt_of_succ_lt_succ]))
      (add unsafe 10% (by grind only [Nat.lt_of_succ_lt]))
      (add unsafe 10% (by grind only [Nat.le_succ_of_le]))
      (add unsafe 10% (by grind only [Nat.zero_le]))
      (add unsafe 10% (by grind only [lt_add_one]))
      (add unsafe 10% (by grind only [Nat.lt_succ_of_lt]))
      (add unsafe 10% (by grind only [Nat.div_lt_self]))
      (add unsafe 10% (by grind only [lt_of_le_of_lt]))
      (add unsafe 10% (by grind only [lt_of_lt_of_le]))
      (add unsafe 10% (by grind only [lt_trans]))
      (add unsafe 10% (by grind only [Pell.strictMono_x]))
      (add unsafe 10% (by grind only [Pell.x_pos]))

  -- Step 5 & 6: Let p = 1
  let p := 1

  -- Step 4: Verify (m - 1)(p - 1) <= 1 implies the inequality condition
  -- We need to show m * p <= m + p
  -- Substituting p = 1: m * 1 <= m + 1 => m <= m + 1, which is always true for natural numbers.

  -- Step 11 & 12: Show m * p <= m + p when p = 1
  have h_step12 : m * p ≤ m + p := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.add_le_add]))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [Std.Range.numElems_le_iff]))
      (add norm 0 (by grind only [Nat.add_le_add_right]))
      (add norm 0 (by rw [mul_le_mul_iff_left]))
      (add unsafe 10% (by grind only [Nat.le_add_left]))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₄]))
      (add unsafe 10% (by grind only [Nat.le_add_right]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₂]))
      (add unsafe 50% (by nlinarith [Nat.mul_le_mul]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₁]))
      (add unsafe 50% (by nlinarith [Ordnode.delta]))
      (add unsafe 50% (by nlinarith [Ordnode.ratio]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₅]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₃]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₄]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₁]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₂]))
      (add unsafe 50% (by nlinarith [Zsqrtd.sqLe_add_mixed]))
      (add unsafe 10% (by grind only [Nat.zero_le]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₃]))
      (add unsafe 10% (by grind only [Nat.succ_le_succ]))
      (add unsafe 50% (by nlinarith [Zsqrtd.SqLe]))
      (add unsafe 10% (by grind only [Ordnode.raised_iff]))
      (add unsafe 10% (by grind only [Nat.le_succ]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.merge_lemma]))
      (add unsafe 10% (by grind only [Nat.succ_le_iff]))
      (add unsafe 10% (by grind only [Nat.le_div_iff_mul_le]))
      (add unsafe 10% (by grind only [Nat.le_of_succ_le_succ]))
      (add unsafe 10% (by grind only [Ordnode.Raised.dist_le]))

  -- Step 13: Combine results
  have h_final : ∃ m, m > n ∧ ∃ p, m * p ≤ m + p := by
    clear * - h_step10 h_step12
    exact ⟨m, h_step10, p, h_step12⟩

  exact h_final
