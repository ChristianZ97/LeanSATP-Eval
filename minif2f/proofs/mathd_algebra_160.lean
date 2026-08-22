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


theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    maxGoals := 512
    enableSimp := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 100 (by exfalso))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [mul_left_comm]))
    (add norm 0 (by grind only [mul_assoc]))
    (add norm 0 (by grind only [mul_right_comm]))
    (add norm 0 (by grind only [mul_comm]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [Quaternion.star_add_self]))
    (add norm 0 (by grind only [Quaternion.self_add_star]))
    (add norm 0 (by grind only [mul_two]))
    (add norm 0 (by grind only [Quaternion.star_add_self']))
    (add norm 0 (by rw [Quaternion.coe_commutes]))
    (add norm 0 (by grind only [mul_lt_mul_iff_left]))
    (add norm 0 (by grind only [Quaternion.self_add_star']))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
    (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
    (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
    (add norm 0 (by grind only [jacobiTheta₂_term]))
    (add norm 0 (by grind only [ack_two]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
    (add norm 0 (by rw [mul_self]))
    (add norm 0 (by grind only [Pell.isPell_norm]))
    (add norm 0 (by grind only [Pell.Solution₁.y_mul]))
    (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
    (add norm 0 (by grind only [Real.Angle.coe_two_pi]))
    (add norm 0 (by grind only [Pell.Solution₁.x_mul]))
    (add norm 0 (by grind only [QuaternionAlgebra.mul_re]))
    (add norm 0 (by grind only [mul_le_mul_left]))
    (add norm 0 (by grind only [mul_mul_mul_comm]))
    (add norm 0 (by rw [Quaternion.coe_add]))
    (add norm 0 (by rw [mul_le_mul_iff_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
