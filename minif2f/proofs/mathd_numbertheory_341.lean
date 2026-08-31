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


theorem mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) : a + b + c = 13 := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by push_neg))
    (add safe 100 (by zify))
    (add safe 100 (by interval_cases))
    (add safe 0 (by ext))
    (add safe 0 (by split))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Nat.digits]))
    (add norm 0 (by grind only [Nat.digits_of_lt]))
    (add norm 0 (by grind only [Nat.one_mul]))
    (add norm 0 (by grind only [Nat.NormDigits.digits_one]))
    (add norm 0 (by grind only [Nat.div_add_mod]))
    (add norm 0 (by grind only [Nat.digits_add]))
    (add norm 0 (by grind only [Nat.mul_one]))
    (add norm 0 (by grind only [Nat.mod_add_div]))
    (add norm 0 (by grind only [Nat.digits_def']))
    (add norm 0 (by grind only [Nat.add_div]))
    (add norm 0 (by grind only [Nat.digits_add_two_add_one]))
    (add norm 0 (by grind only [Nat.div_eq_of_lt]))
    (add norm 0 (by grind only [Nat.digits_eq_cons_digits_div]))
    (add norm 0 (by grind only [Nat.NormDigits.digits_succ]))
    (add norm 0 (by grind only [Nat.le_add_right]))
    (add norm 0 (by grind only [Nat.add_comm]))
    (add norm 0 (by grind only [Num.cast_mul]))
    (add norm 0 (by grind only [Nat.div_add_mod']))
    (add norm 0 (by grind only [Nat.pow_one]))
    (add norm 0 (by grind only [Zsqrtd.SqLe]))
    (add norm 0 (by grind only [Matrix.get_node_cy]))
    (add norm 0 (by grind only [Nat.le_add_left]))
    (add norm 0 (by grind only [Nat.div_mod_unique]))
    (add norm 0 (by grind only [Nat.ofDigits_digits]))
    (add norm 0 (by grind only [Nat.div2_val]))
    (add norm 0 (by grind only [Nat.getLast_digit_ne_zero]))
    (add norm 0 (by grind only [Nat.mul_succ]))
    (add norm 0 (by grind only [Nat]))
    (add norm 0 (by grind only [Nat.ofDigits_one]))
    (add norm 0 (by grind only [Nat.mul_add]))
    (add norm 0 (by grind only [Nat.pow_add]))
    (add norm 0 (by grind only [Nat.digits_zero]))
