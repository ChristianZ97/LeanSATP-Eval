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


theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by

  aesop (config := {
    maxRuleApplications := 100
    maxNormIterations := 320
    maxGoals := 512
    enableSimp := false
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 50% (by ring_nf at *))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [Real.sqrt_sq]))
    (add norm 0 (by grind only [Real.sqrt_mul]))
    (add norm 0 (by grind only [sq_sub_sq]))
    (add norm 0 (by grind only [Real.mul_self_sqrt]))
    (add norm 0 (by grind only [Real.sqrt_mul_self]))
    (add norm 0 (by grind only [sq_abs]))
    (add norm 0 (by grind only [sq_eq_sq]))
    (add norm 0 (by grind only [Real.sqrt_mul']))
    (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
    (add norm 0 (by grind only [sq_nonneg]))
    (add norm 0 (by grind only [norm_add_sq]))
    (add norm 0 (by grind only [Real.sqrt_nonneg]))
    (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
    (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
    (add norm 0 (by grind only [norm_add_sq_real]))
    (add norm 0 (by grind only [EuclideanSpace.dist_eq]))
    (add norm 0 (by grind only [sub_sq]))
    (add norm 0 (by grind only [sq_lt_sq]))
    (add norm 0 (by grind only [sq_le_sq]))
    (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
    (add norm 0 (by grind only [norm_sub_sq]))
    (add norm 0 (by grind only [Real.sqrt]))
    (add norm 0 (by grind only [norm_sub_sq_real]))
    (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
    (add norm 0 (by grind only [UpperHalfPlane.dist_coe_center_sq]))
    (add norm 0 (by grind only [aux_add]))
    (add norm 0 (by grind only [Real.cos_half]))
    (add unsafe 90% (by simp only [Real.rpow_two] at *))
    (add unsafe 90% (by simp only [pow_two] at *))
    (add unsafe 50% (by simp only [sq_add_sq_mul]))
    (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))
