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


theorem mathd_algebra_329 (x y : ℝ) (h₀ : 3 * y = x) (h₁ : 2 * x + 5 * y = 11) : x + y = 4 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableSimp := false
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
    (add safe 0 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by exfalso))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [Quaternion.star_add_self]))
    (add norm 0 (by grind only [Quaternion.self_add_star]))
    (add norm 0 (by grind only [mul_two]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [pow_two]))
    (add norm 0 (by grind only [mul_comm]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
    (add norm 0 (by grind only [zero_lt_two]))
    (add norm 0 (by grind only [zero_lt_two']))
    (add norm 0 (by grind only [Quaternion.star_add_self']))
    (add norm 0 (by grind only [two_ne_zero']))
    (add norm 0 (by grind only [Quaternion.self_add_star']))
    (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
    (add norm 0 (by grind only [Real.sin_two_mul]))
    (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [mul_left_comm]))
    (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
    (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
    (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
    (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero_z]))
    (add norm 0 (by grind only [Real.Angle.coe_two_pi]))
    (add norm 0 (by grind only [Complex.two_cosh]))
    (add norm 0 (by grind only [Complex.two_sinh]))
    (add norm 0 (by grind only [EisensteinSeries.r1]))
    (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
    (add norm 0 (by grind only [Quaternion.star_eq_two_re_sub]))
    (add norm 0 (by grind only [mul_right_comm]))
    (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
    (add unsafe 50% (by simp only [sq_add_sq_mul]))
