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


theorem amc12b_2002_p7 (a b c : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : b = a + 1) (h₂ : c = b + 1)
    (h₃ : a * b * c = 8 * (a + b + c)) : a ^ 2 + (b ^ 2 + c ^ 2) = 77 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 380
    maxNormIterations := 320
    maxGoals := 512
    enableSimp := false
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by bound))
    (add norm 0 (by split))
    (add norm 0 (by simp_all))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by ext))
    (add safe 100 (by exfalso))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [mul_assoc]))
    (add norm 0 (by grind only [mul_left_comm]))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [mul_comm]))
    (add norm 0 (by grind only [mul_right_comm]))
    (add norm 0 (by grind only [mul_pow]))
    (add norm 0 (by grind only [mul_two]))
    (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
    (add norm 0 (by grind only [pow_add]))
    (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
    (add norm 0 (by grind only [ack_two]))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
    (add norm 0 (by grind only [sq_add_sq_mul]))
    (add norm 0 (by grind only [even_two]))
    (add norm 0 (by grind only [zero_lt_two]))
    (add norm 0 (by grind only [Nat.cast_two]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
    (add norm 0 (by rw [mul_one]))
    (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
    (add norm 0 (by grind only [Quaternion.self_add_star]))
    (add norm 0 (by grind only [Nat.succ_mul]))
    (add norm 0 (by grind only [Nat.sq_add_sq_mul]))
    (add norm 0 (by grind only [Nat.pow_succ']))
    (add norm 0 (by grind only [Nat.two_mul]))
    (add norm 0 (by grind only [quadraticChar_sq_one]))
    (add norm 0 (by grind only [mul_le_mul_left]))
    (add norm 0 (by grind only [even_two_mul]))
    (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf]))
    (add unsafe 90% (by simp only [pow_two] at *))
