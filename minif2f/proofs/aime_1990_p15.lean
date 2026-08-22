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


theorem aime_1990_p15 (a b x y : ℝ) (h₀ : a * x + b * y = 3) (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16) (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableSimp := false
    enableUnfold := false
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 0 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [sq_pos_of_pos]))
    (add norm 0 (by grind only [sq_lt_sq]))
    (add norm 0 (by grind only [Real.sq_sqrt]))
    (add norm 0 (by grind only [Real.sqrt_lt]))
    (add norm 0 (by grind only [Pell.Solution₁.y_mul]))
    (add norm 0 (by grind only [EisensteinSeries.r1]))
    (add norm 0 (by grind only [sq_abs]))
    (add norm 0 (by grind only [sq_sub_sq]))
    (add norm 0 (by grind only [mul_self_nonneg]))
    (add norm 0 (by grind only [one_lt_sq_iff_one_lt_abs]))
    (add norm 0 (by grind only [sq_eq_sq]))
    (add norm 0 (by grind only [Real.sqrt_sq]))
    (add norm 0 (by grind only [Real.lt_sqrt]))
    (add norm 0 (by grind only [Pell.Solution₁.x_mul]))
    (add norm 0 (by grind only [euler_four_squares]))
    (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
    (add norm 0 (by grind only [sq_lt_one_iff]))
    (add norm 0 (by grind only [Real.mul_self_sqrt]))
    (add norm 0 (by grind only [zero_lt_two]))
    (add unsafe 50% (by simp only [sq_add_sq_mul]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
    (add unsafe 50% (by nlinarith [Pell.Solution₁.x_mul_pos]))
    (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
    (add unsafe 50% (by nlinarith [Real.mul_pos]))
    (add unsafe 90% (by simp only [pow_two] at *))
    (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
    (add unsafe 50% (by nlinarith [EisensteinSeries.r1_pos]))
    (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
