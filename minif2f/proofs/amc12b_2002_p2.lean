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


theorem amc12b_2002_p2 (x : ℤ) (h₀ : x = 4) :
    (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    maxGoals := 512
    enableSimp := false
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
    (add safe 100 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by exfalso))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [mul_div_cancel_right]))
    (add norm 0 (by grind only [div_mul]))
    (add norm 0 (by grind only [mul_div_cancel_left]))
    (add norm 0 (by grind only [mul_div_cancel]))
    (add norm 0 (by grind only [sub_eq_add]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [div_eq_iff_eq_mul]))
    (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
    (add norm 0 (by grind only [QuaternionGroup.xa_mul_xa]))
    (add norm 0 (by grind only [Pell.d]))
    (add norm 0 (by grind only [div_mul_cancel]))
    (add norm 0 (by grind only [Real.Angle.coe_sub]))
    (add norm 0 (by grind only [AddConstMapClass.map_add_zsmul]))
    (add norm 0 (by grind only [div_self']))
    (add norm 0 (by grind only [mul_comm]))
    (add norm 0 (by grind only [mul_right_comm]))
    (add norm 0 (by grind only [AddConstMapClass.map_sub_zsmul]))
    (add norm 0 (by grind only [mul_assoc]))
    (add norm 0 (by grind only [Int.modEq_add_fac]))
    (add norm 0 (by grind only [mul_left_comm]))
    (add norm 0 (by grind only [div_eq_mul_inv]))
    (add norm 0 (by grind only [AddConstMapClass.map_sub_const]))
    (add norm 0 (by grind only [Pell.isPell_norm]))
    (add norm 0 (by grind only [div_inv_eq_mul]))
    (add norm 0 (by grind only [div_one]))
    (add norm 0 (by grind only [AddConstMapClass.map_sub_int']))
    (add safe 0 (by simp only [div_div] at *))
    (add safe 0 (by simp only [mul_div] at *))
    (add safe 0 (by simp only [mul_div_assoc] at *))
    (add safe 0 (by simp only [sub_div] at *))
    (add unsafe 50% (by grind only [Int.emod_add_ediv]))
    (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))
