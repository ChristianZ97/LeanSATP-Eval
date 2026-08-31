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


theorem aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₁ : x ^ 2 - 10 * x - 29 ≠ 0)
    (h₂ : x ^ 2 - 10 * x - 45 ≠ 0) (h₃ : x ^ 2 - 10 * x - 69 ≠ 0)
    (h₄ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0) :
    x = 13 := by

  aesop (config := {
    maxRuleApplications := 100
    maxRuleApplicationDepth := 10
    maxNormIterations := 520
    maxGoals := 256
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
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [mul_right_inj']))
    (add norm 0 (by grind only [irrational_iff_ne_rational]))
    (add norm 0 (by grind only [Iff]))
    (add norm 0 (by grind only [mul_left_cancel₀]))
    (add norm 0 (by grind only [sq_eq_zero_iff]))
    (add norm 0 (by grind only [sq_pos_of_pos]))
    (add norm 0 (by grind only [div_eq_one]))
    (add norm 0 (by grind only [two_ne_zero]))
    (add norm 0 (by grind only [sq_eq_sq]))
    (add norm 0 (by grind only [mul_left_inj']))
    (add norm 0 (by grind only [div_ne_one_of_ne]))
    (add norm 0 (by grind only [Int.sq_of_gcd_eq_one]))
    (add norm 0 (by grind only [mul_right_cancel₀]))
    (add norm 0 (by grind only [div_ne_one]))
    (add norm 0 (by grind only [pow_ne_zero]))
    (add norm 0 (by grind only [mul_eq_one_iff']))
    (add norm 0 (by grind only [mul_ne_zero]))
    (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
    (add norm 0 (by grind only [legendreSym.eq_zero_mod_of_eq_neg_one]))
    (add norm 0 (by grind only [LucasLehmer.mersenne_int_ne_zero]))
    (add norm 0 (by grind only [sq_pos_iff]))
    (add norm 0 (by grind only [sq_eq_one_iff]))
    (add norm 0 (by grind only [WeierstrassCurve.Jacobian.Y_sub_Y_mul_Y_sub_negY]))
    (add norm 0 (by grind only [eq_div_iff_mul_eq]))
    (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
    (add norm 0 (by grind only [FractionalIdeal.mem_div_iff_of_nonzero]))
    (add norm 0 (by grind only [WeierstrassCurve.Affine.Y_eq_of_Y_ne]))
    (add safe 0 (by simp only [div_ne_zero] at *))
    (add unsafe 50% (by nlinarith [mul_nonneg_iff_of_pos_right]))
    (add unsafe 50% (by nlinarith [mul_self_pos]))
    (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
    (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
