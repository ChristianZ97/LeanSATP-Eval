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


theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [div_eq_one]))
    (add norm 0 (by grind only [div_eq_iff_eq_mul]))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [div_eq_iff_eq_mul']))
    (add norm 0 (by grind only [mul_two]))
    (add norm 0 (by grind only [Real.Angle.coe_sub]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [two_ne_zero']))
    (add norm 0 (by rw [Quaternion.coe_sub]))
    (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
    (add norm 0 (by grind only [Quaternion.star_add_self]))
    (add norm 0 (by grind only [Real.Angle.angle_eq_iff_two_pi_dvd_sub]))
    (add norm 0 (by grind only [Quaternion.self_add_star]))
    (add norm 0 (by grind only [Real.two_mul_arctan]))
    (add norm 0 (by grind only [one_add_one_eq_two]))
    (add norm 0 (by grind only [div_self']))
    (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
    (add norm 0 (by grind only [Real.sin_two_mul]))
    (add norm 0 (by grind only [Int.cast_two]))
    (add norm 0 (by grind only [Ideal.toCotangent_eq]))
    (add norm 0 (by grind only [Ring.multichoose_two]))
    (add norm 0 (by grind only [Nat.cast_two]))
    (add norm 0 (by grind only [add_halves]))
    (add norm 0 (by grind only [mul_div_cancel_left]))
    (add norm 0 (by grind only [Quaternion.star_add_self']))
    (add norm 0 (by grind only [Nat.factorial_two]))
    (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
    (add norm 0 (by grind only [mul_div_cancel]))
    (add norm 0 (by grind only [Complex.sin_two_mul]))
    (add norm 0 (by grind only [Quaternion.self_add_star']))
    (add norm 0 (by grind only [CharTwo.two_eq_zero]))
    (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))
