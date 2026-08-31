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


theorem aime_1989_p8 (a b c d e f g : ℝ)
    (h₀ : a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g = 1)
    (h₁ : 4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g = 12)
    (h₂ : 9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g = 123) :
    16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    maxGoals := 512
    enableSimp := false
    }) (rule_sets := [-builtin])
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 100 (by decide))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [mul_left_comm]))
    (add norm 0 (by grind only [mul_right_comm]))
    (add norm 0 (by grind only [mul_assoc]))
    (add norm 0 (by grind only [mul_comm]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
    (add norm 0 (by grind only [Pell.isPell_norm]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
    (add norm 0 (by grind only [Pell.Solution₁.y_mul]))
    (add norm 0 (by grind only [Pell.Solution₁.x_mul]))
    (add norm 0 (by grind only [mul_mul_mul_comm]))
    (add norm 0 (by grind only [Quaternion.star_add_self]))
    (add norm 0 (by grind only [Quaternion.self_add_star]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_re]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imK]))
    (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero_z]))
    (add norm 0 (by grind only [Real.Angle.coe_two_pi]))
    (add norm 0 (by rw [Quaternion.coe_commutes]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
    (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt]))
    (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt']))
    (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
    (add unsafe 50% (by nlinarith [div_lt_iff_lt_mul']))
    (add unsafe 50% (by nlinarith [mul_le_mul_left]))
    (add unsafe 50% (by nlinarith [div_lt_iff_lt_mul]))
    (add unsafe 50% (by nlinarith [Real.arctan_ne_mul_pi_div_two]))
    (add unsafe 50% (by nlinarith [div_lt_iff]))
    (add unsafe 50% (by nlinarith [lt_div_iff]))
    (add unsafe 50% (by nlinarith [Real.add_lt_add_iff_left]))
