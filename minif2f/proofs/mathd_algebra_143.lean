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


theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableSimp := false
    enableUnfold := false
    })
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by norm_cast))
    (add safe 100 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [even_two]))
    (add norm 0 (by grind only [zero_lt_two]))
    (add norm 0 (by grind only [integral_gaussian]))
    (add norm 0 (by rw [Quaternion.coe_one]))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [sq_eq_sq]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
    (add norm 0 (by grind only [sq_abs]))
    (add norm 0 (by grind only [Real.sqrt_sq]))
    (add norm 0 (by grind only [Real.exp_half]))
    (add norm 0 (by grind only [Real.rpow_one]))
    (add norm 0 (by grind only [Real.exp_zero]))
    (add norm 0 (by grind only [Quaternion.coe_re]))
    (add norm 0 (by grind only [sq_sub_sq]))
    (add norm 0 (by grind only [Polynomial.cyclotomic_two]))
    (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [Real.Gamma]))
    (add norm 0 (by grind only [integral_id]))
    (add unsafe 90% (by simp only [Real.Gamma_two] at *))
    (add unsafe 90% (by simp only [Real.rpow_two] at *))
    (add unsafe 90% (by simp only [ArithmeticFunction.moebius_sq] at *))
    (add unsafe 90% (by simp only [pow_two] at *))
    (add unsafe 90% (by simp only [Nat.factorial_two] at *))
    (add unsafe 90% (by simp only [sq_eq_one_iff] at *))
    (add unsafe 90% (by simp only [Nat.cast_two] at *))
    (add unsafe 50% (by simp only [sq_add_sq_mul]))
    (add unsafe 90% (by simp only [CoxeterSystem.simple_sq] at *))
    (add unsafe 90% (by simp only [EuclideanSpace.norm_eq] at *))
    (add unsafe 90% (by simp only [Polynomial.derivative_sq] at *))
    (add unsafe 90% (by simp only [zero_le_two] at *))
