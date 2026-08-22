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


theorem mathd_numbertheory_135 (n A B C : ℕ) (h₀ : n = 3 ^ 17 + 3 ^ 10) (h₁ : 11 ∣ n + 1)
    (h₂ : [A, B, C].Pairwise (· ≠ ·)) (h₃ : {A, B, C} ⊂ Finset.Icc 0 9) (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬3 ∣ B) (h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]) :
    100 * A + 10 * B + C = 129 := by

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
    (add norm 1 (by ext))
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
    (add norm 0 (by grind only [mul_left_comm]))
    (add norm 0 (by grind only [mul_right_comm]))
    (add norm 0 (by grind only [mul_comm]))
    (add norm 0 (by grind only [mul_assoc]))
    (add norm 0 (by grind only [Nat.div_add_mod]))
    (add norm 0 (by grind only [Pell.d]))
    (add norm 0 (by grind only [Nat.div_add_mod']))
    (add norm 0 (by grind only [Zsqrtd.SqLe]))
    (add norm 0 (by grind only [Nat.succ_mul]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [Zsqrtd.not_divides_sq]))
    (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
    (add norm 0 (by grind only [Nat.mod_add_div]))
    (add norm 0 (by grind only [Nat.add_sub_of_le]))
    (add norm 0 (by grind only [Pell.dz_val]))
    (add norm 0 (by grind only [Zsqrtd.sqLe_smul]))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [Nat.add_sub_assoc]))
    (add norm 0 (by grind only [Pell.isPell_norm]))
    (add norm 0 (by grind only [Nat.succ_mul_centralBinom_succ]))
    (add norm 0 (by grind only [Nat.mul_one]))
    (add norm 0 (by grind only [Nat.left_distrib]))
    (add norm 0 (by grind only [Nat.mul_add]))
    (add norm 0 (by grind only [tsub_add_cancel_of_le]))
    (add norm 0 (by grind only [Eq.symm]))
    (add norm 0 (by grind only [Nat.le_add_left]))
    (add norm 0 (by rw [Pell.pellZd]))
    (add norm 0 (by grind only [Nat.add_le_add]))
    (add norm 0 (by grind only [Nat.add_sub_cancel']))
    (add norm 0 (by grind only [Nat.mul_succ]))
    (add unsafe 10% (by grind only [Pell.xn]))
    (add unsafe 50% (by nlinarith [Nat.mul_le_mul_left]))
