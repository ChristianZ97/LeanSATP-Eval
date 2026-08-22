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


theorem mathd_algebra_314 (n : ℕ) (h₀ : n = 11) : (1 / 4 : ℚ) ^ (n + 1) * 2 ^ (2 * n) = 1 / 4 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 380
    maxNormIterations := 520
    maxGoals := 512
    enableSimp := false
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by bound))
    (add norm 0 (by simp_all))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by ext))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 50% (by ring_nf at *))
    (add norm 0 (by grind only [one_pow]))
    (add norm 0 (by rw [one_mul]))
    (add norm 0 (by rw [mul_one]))
    (add norm 0 (by grind only [pow_add]))
    (add norm 0 (by grind only [pow_mul]))
    (add norm 0 (by grind only [neg_one_sq]))
    (add norm 0 (by grind only [LucasLehmer.X.ω]))
    (add norm 0 (by grind only [mul_pow]))
    (add norm 0 (by grind only [Even.neg_one_pow]))
    (add norm 0 (by grind only [pow_one]))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
    (add norm 0 (by grind only [pow_succ]))
    (add norm 0 (by grind only [FractionalIdeal.count_pow]))
    (add norm 0 (by grind only [pow_succ']))
    (add norm 0 (by grind only [PerfectClosure.mk_pow]))
    (add norm 0 (by grind only [LucasLehmer.X.ωb]))
    (add norm 0 (by grind only [neg_pow]))
    (add norm 0 (by grind only [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq]))
    (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
    (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
    (add norm 0 (by grind only [geom_sum₂_with_one]))
    (add norm 0 (by grind only [quadraticChar_sq_one]))
    (add norm 0 (by grind only [QuaternionGroup.a_one_pow]))
    (add norm 0 (by grind only [legendreSym.sq_one]))
    (add norm 0 (by grind only [Nat.pow_succ']))
    (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
    (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
    (add norm 0 (by grind only [mul_assoc]))
    (add norm 0 (by grind only [IsNilpotent.pow_succ]))
    (add norm 0 (by grind only [qrSign.sq_eq_one]))
    (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
    (add norm 0 (by grind only [one_div]))
