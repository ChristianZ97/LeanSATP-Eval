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


theorem mathd_algebra_296 : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableSimp := false
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 10% (by exfalso))
    (add norm 0 (by grind only [sq_sub_sq]))
    (add norm 0 (by grind only [abs_sq]))
    (add norm 0 (by grind only [sq_lt_sq]))
    (add norm 0 (by grind only [sq_abs]))
    (add norm 0 (by grind only [sub_sq]))
    (add norm 0 (by grind only [sq_le_sq]))
    (add norm 0 (by grind only [norm_add_sq_real]))
    (add norm 0 (by grind only [mabs_of_one_lt]))
    (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [norm_sub_sq_real]))
    (add norm 0 (by grind only [aux_add]))
    (add norm 0 (by grind only [abs_mul]))
    (add norm 0 (by grind only [Real.abs_sin_half]))
    (add norm 0 (by grind only [Complex.sq_abs]))
    (add norm 0 (by grind only [Real.sqrt_sq]))
    (add norm 0 (by grind only [abs_two]))
    (add norm 0 (by grind only [pow_two]))
    (add norm 0 (by grind only [UpperHalfPlane.dist_coe_center_sq]))
    (add norm 0 (by grind only [norm_add_sq]))
    (add norm 0 (by grind only [EisensteinSeries.auxbound1]))
    (add norm 0 (by grind only [EisensteinSeries.auxbound2]))
    (add norm 0 (by grind only [mabs_div_comm]))
    (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
    (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
    (add unsafe 50% (by simp only [sq_add_sq_mul]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
    (add unsafe 90% (by simp only [Real.rpow_two] at *))
    (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))
    (add unsafe 50% (by simp only [Int.sq_eq_one_of_sq_le_three]))
