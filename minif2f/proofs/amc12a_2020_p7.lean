
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


set_option maxHeartbeats 0

theorem amc12a_2020_p7 (a : ℕ → ℕ) (h₀ : a 0 ^ 3 = 1) (h₁ : a 1 ^ 3 = 8) (h₂ : a 2 ^ 3 = 27)
    (h₃ : a 3 ^ 3 = 64) (h₄ : a 4 ^ 3 = 125) (h₅ : a 5 ^ 3 = 216) (h₆ : a 6 ^ 3 = 343) :
    (↑(∑ k ∈ Finset.range 7, 6 * a k ^ 2 :) - ↑(2 * ∑ k ∈ Finset.range 6, a k ^ 2 :)) = (658 : ℤ) := by
  -- Step 1: Prove a(0) = 1
  have h_a0 : a 0 = 1 := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [zero_pow]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
      (add norm 0 (by grind only [LucasLehmer.s]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [pow_zero]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [DihedralGroup.one_def]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [pow_one]))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by grind only [PerfectClosure.one_def]))
      (add norm 0 (by grind only [DirectSum.of_zero_pow]))
      (add norm 0 (by grind only [QuaternionGroup.one_def]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [pow_eq_zero]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_apply_of_squarefree]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
      (add norm 0 (by grind only [FiniteField.pow_card]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))

  -- Step 2: Prove a(1) = 2
  have h_a1 : a 1 = 2 := by
    clear * - h₁
    nlinarith [sq_nonneg <| a 1 ^ 2, h₁]

  -- Step 3: Prove a(2) = 3
  have h_a2 : a 2 = 3 := by
    clear * - h₂
    nlinarith [sq_nonneg (a 2), sq_nonneg (a 2 - 3)]

  -- Step 4: Prove a(3) = 4
  have h_a3 : a 3 = 4 := by
    clear * - h₃
    nlinarith [(sq_nonneg (a 3)), sq_nonneg (a 3 ^ 2)]

  -- Step 5: Prove a(4) = 5
  have h_a4 : a 4 = 5 := by
    clear * - h₄
    have hv := h₄
    nlinarith [sq_nonneg (a 4), sq_nonneg (a 4 ^ 2)]

  -- Step 6: Prove a(5) = 6
  have h_a5 : a 5 = 6 := by
    clear * - h₅
    nlinarith [sq_nonneg (a 5 ^ 2)]

  -- Step 7: Prove a(6) = 7
  have h_a6 : a 6 = 7 := by
    clear * - h₆
    nlinarith [sq_nonneg (a 6), sq_nonneg (a 6 ^ 2), h₆]

  -- Step 8: Compute a(0)^2 = 1
  have h_sq0 : a 0 ^ 2 = 1 := by
    clear * - h_a0
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [zero_pow]))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [LucasLehmer.s]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [pow_one]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
      (add norm 0 (by grind only [FiniteField.pow_card]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [FractionalIdeal.count_pow]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [pow_zero]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [QuaternionGroup.one_def]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [DihedralGroup.one_def]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))

  -- Step 9: Compute a(1)^2 = 4
  have h_sq1 : a 1 ^ 2 = 4 := by
    clear * - h_a1
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 0 (by assumption_mod_cast))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [pow_one]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_apply_of_squarefree]))
      (add norm 0 (by grind only [DihedralGroup.r_one_pow_n]))
      (add norm 0 (by grind only [DihedralGroup.r_one_pow]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [AlgebraicGeometry.Proj.pow_apply]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
      (add norm 0 (by grind only [ppow_one]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [geom_sum₂_with_one]))
      (add norm 0 (by grind only [QuaternionGroup.one_def]))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [PerfectClosure.one_def]))
      (add norm 0 (by grind only [ArithmeticFunction.cardDistinctFactors_apply_prime_pow]))
      (add norm 0 (by grind only [Polynomial.eval_one_cyclotomic_prime_pow]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))
      (add norm 0 (by grind only [frobenius_one]))
      (add safe 1 (by simp only [ZMod.neg_one_pow_div_two_of_one_mod_four] at *))

  -- Step 10: Compute a(2)^2 = 9
  have h_sq2 : a 2 ^ 2 = 9 := by
    clear * - h_a2
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_one_mod_four]))
      (add norm 0 (by grind only [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  -- Step 11: Compute a(3)^2 = 16
  have h_sq3 : a 3 ^ 2 = 16 := by
    clear * - h_a3
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
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
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [pow_two_pow_sub_pow_two_pow]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))

  -- Step 12: Compute a(4)^2 = 25
  have h_sq4 : a 4 ^ 2 = 25 := by
    clear * - h_a4
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [pow_pos]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq]))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))

  -- Step 13: Compute a(5)^2 = 36
  have h_sq5 : a 5 ^ 2 = 36 := by
    clear * - h_a5
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 0 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [pow_two_pow_sub_pow_two_pow]))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [IsSquare_sq]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))

  -- Step 14: Compute a(6)^2 = 49
  have h_sq6 : a 6 ^ 2 = 49 := by
    clear * - h_a6
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 0 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by grind only [Pell.Solution₁.prop]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
      (add norm 0 (by grind only [FiniteField.pow_card]))
      (add norm 0 (by grind only [FractionalIdeal.count_pow]))
      (add norm 0 (by grind only [Int.units_sq]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  -- Step 15 & 16: Sum of squares from k=0 to 5 is 91
  have h_sum5 : (∑ k ∈ Finset.range 6, a k ^ 2) = 91 := by
    clear * - h_sq0 h_sq1 h_sq2 h_sq3 h_sq4 h_sq5
    have h0 : a 0 = 1
    ·
      classical
      have : a 0 ^ 2 = 1 := h_sq0
      have h0 : a 0 = 1 := by nlinarith
      assumption
    · have h1 : a 1 = 2 := by nlinarith
      try simp_all [Finset.range_succ]

  -- Step 17 & 18: Sum of squares from k=0 to 6 is 140
  have h_sum6 : (∑ k ∈ Finset.range 7, a k ^ 2) = 140 := by
    clear * - h_sum5 h_sq6
    simp_all [Finset.sum_range_succ] <;> norm_cast

  -- Step 19 & 20: 6 * sum_{k=0}^6 a(k)^2 = 840
  have h_term1 : 6 * (∑ k ∈ Finset.range 7, a k ^ 2) = 840 := by
    clear * - h_sum6
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
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
      (add norm 0 (by split))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by exfalso))
      (add safe 100 (by simp_all))
      (add safe 100 (by ring_nf at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [add_pow]))
      (add norm 0 (by grind only [Nat.choose_self]))
      (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [Finset.prod_range_one]))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [geom_sum_mul_add]))
      (add norm 0 (by grind only [Finset.range_one]))
      (add norm 0 (by grind only [Finset.range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_zero]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
      (add norm 0 (by grind only [Finset.range_add_one]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [geom_sum₂_with_one]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
      (add norm 0 (by grind only [sum_range_pow]))
      (add norm 0 (by grind only [bernsteinPolynomial.sum]))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
      (add norm 0 (by grind only [numDerangements]))
      (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
      (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
      (add norm 0 (by grind only [Nat.choose_zero_right]))
      (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
      (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))

  -- Step 21 & 22: 2 * sum_{k=0}^5 a(k)^2 = 182
  have h_term2 : 2 * (∑ k ∈ Finset.range 6, a k ^ 2) = 182 := by
    clear * - h_sum5
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 16
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by ring_nf at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [add_pow]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [Nat.choose_self]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [geom_sum_mul_add]))
      (add norm 0 (by grind only [Finset.range_succ]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Finset.range_add_one]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [geom_sum₂_with_one]))
      (add norm 0 (by grind only [Finset.prod_range_one]))
      (add norm 0 (by grind only [Finset.range_one]))
      (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [Finset.prod_range_zero]))
      (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
      (add norm 0 (by grind only [Nat.sum_range_choose]))
      (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
      (add norm 0 (by grind only [Nat.factorial]))
      (add norm 0 (by grind only [Finset.mul_sum]))

  -- Step 23: Difference is 658
  have h_final : (6 * (∑ k ∈ Finset.range 7, a k ^ 2) : ℤ) - (2 * (∑ k ∈ Finset.range 6, a k ^ 2) : ℤ) = 658 := by
    clear * - h_term1 h_term2
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 60
      maxGoals := 16
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by ring_nf at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [numDerangements_sum]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [mul_geom_sum]))
      (add norm 0 (by grind only [Finset.prod_range_succ_div_prod]))
      (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add norm 0 (by grind only [Nat.cast_sum]))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [add_pow]))
      (add norm 0 (by grind only [Finset.sum_mul]))
      (add norm 0 (by grind only [sum_range_pow]))
      (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
      (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt]))
      (add norm 0 (by grind only [geom_sum_mul]))
      (add norm 0 (by grind only [binomial_sum_eq]))
      (add norm 0 (by grind only [Finset.sum_range_reflect]))
      (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
      (add norm 0 (by grind only [Finset.sum_range_id]))
      (add norm 0 (by grind only [bernsteinPolynomial.sum_mul_smul]))
      (add norm 0 (by grind only [Finset.prod_const]))
      (add norm 0 (by grind only [summable_powerSeries_of_norm_lt_one]))
      (add norm 0 (by grind only [bernsteinPolynomial.sum_smul]))
      (add norm 0 (by grind only [geom_sum_mul_add]))
      (add norm 0 (by grind only [Finset.prod_div_distrib]))
      (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
      (add unsafe 50% (by simp only [pow_two_pow_sub_pow_two_pow]))

  -- exact h_final
  simp_all [Finset.range_succ, Finset.sum_insert, Finset.sum_singleton]
