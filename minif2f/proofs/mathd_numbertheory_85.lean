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


theorem mathd_numbertheory_85 : 1 * 3 ^ 3 + 2 * 3 ^ 2 + 2 * 3 + 2 = 53 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 20
    maxNormIterations := 60
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 100 (by exfalso))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by omega))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 1 (by ring_nf at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [euler_four_squares]))
    (add norm 0 (by grind only [add_sq]))
    (add norm 0 (by grind only [even_two_mul]))
    (add norm 0 (by grind only [Nat.euler_four_squares]))
    (add norm 0 (by grind only [sq_add_sq_mul_sq_add_sq]))
    (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
    (add norm 0 (by grind only [add_sq']))
    (add norm 0 (by grind only [Int.two_pow_two_pow_add_two_pow_two_pow]))
    (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
    (add norm 0 (by grind only [Nat.sq_add_sq_mul]))
    (add norm 0 (by grind only [FermatLastTheoremForThreeGen.a_cube_add_b_cube_eq_mul]))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
    (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
    (add norm 0 (by grind only [even_two]))
    (add norm 0 (by grind only [sum_four_sq_mul_sum_four_sq]))
    (add norm 0 (by grind only [sum_eight_sq_mul_sum_eight_sq]))
    (add norm 0 (by grind only [two_mul]))
    (add norm 0 (by grind only [Quaternion.self_add_star]))
    (add norm 0 (by grind only [mul_add_mul]))
    (add norm 0 (by grind only [Int.sq_add_sq_of_two_mul_sq_add_sq]))
    (add norm 0 (by grind only [ack_two]))
    (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
    (add norm 0 (by grind only [sq_sub_sq]))
    (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
    (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
    (add norm 0 (by grind only [Int.isUnit_sq]))
    (add norm 0 (by grind only [Pell.Solution₁.prop_y]))
    (add norm 0 (by grind only [Int.sq_eq_one_of_sq_le_three]))
    (add unsafe 50% (by simp only [sq_add_sq_mul]))
    (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))
    (add unsafe 90% (by simp only [pow_two] at *))
    (add unsafe 50% (by nlinarith [ZMod.neg_one_pow_div_two_of_three_mod_four]))
