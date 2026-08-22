
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

theorem aime_1997_p9 (a : ℝ) (h₀ : 0 < a)
    (h₁ : 1 / a - Int.floor (1 / a) = a ^ 2 - Int.floor (a ^ 2)) (h₂ : 2 < a ^ 2) (h₃ : a ^ 2 < 3) :
    a ^ 12 - 144 * (1 / a) = 233 := by
  -- Step 1: Establish that floor(a^2) = 2
  have h_floor_a_sq : Int.floor (a ^ 2) = 2 := by
    clear * - h₂ h₃
    rewrite [Int.floor_eq_iff]
    exact ⟨h₂.le, by norm_num; linarith⟩

  -- Step 2: Establish that floor(1/a) = 0
  have h_floor_inv_a : Int.floor (1 / a) = 0 := by
    clear * - h₀ h₂ h₃
    apply Int.floor_eq_iff.2
    split_ands <;> field_simp [h₀, h₂, h₃]
    · norm_num [h₀, h₂, h₃] <;> nlinarith
    · norm_num [h₀] <;> nlinarith

  -- Step 3: Derive 1/a = a^2 - 2
  have h_eq_basic : (1 / a : ℝ) = a ^ 2 - 2 := by
    clear * - h₁ h_floor_a_sq h_floor_inv_a
    symm at h₁ ⊢ <;> simp_all

  -- Step 4: Convert to polynomial a^3 - 2a - 1 = 0
  have h_poly_cubic : a ^ 3 - 2 * a - 1 = 0 := by
    clear * - h_eq_basic h₀
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableSimp := false
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [div_eq_one]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [zero_pow]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [integral_id]))
      (add norm 0 (by grind only [zero_div]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [pow_eq_zero]))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))

  -- Step 5: Factorization (a + 1)(a^2 - a - 1) = 0
  have h_factored : (a + 1) * (a ^ 2 - a - 1) = 0 := by
    clear * - h_poly_cubic
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [div_eq_one]))
      (add norm 0 (by grind only [legendreSym.eq_zero_mod_of_eq_neg_one]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [zero_pow]))
      (add norm 0 (by grind only [quadratic_eq_zero_iff_of_discrim_eq_zero]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [MulZeroClass]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [IsCyclotomicExtension.Rat.Three.lambda_sq]))
      (add norm 0 (by grind only [mul_left_cancel₀]))
      (add norm 0 (by grind only [mul_right_inj']))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [WeierstrassCurve.Jacobian.Y_sub_Y_mul_Y_sub_negY]))
      (add norm 0 (by grind only [Zsqrtd.zero_re]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [pow_ne_zero]))
      (add norm 0 (by grind only [discrim]))
      (add norm 0 (by grind only [mul_eq_one_iff']))
      (add norm 0 (by grind only [WeierstrassCurve.Jacobian.equation_of_Z_eq_zero]))
      (add norm 0 (by grind only [quadratic_eq_zero_iff]))
      (add norm 0 (by grind only [pow_eq_zero]))
      (add norm 0 (by grind only [Int.sq_of_gcd_eq_one]))
      (add norm 0 (by grind only [WeierstrassCurve.ψ_zero]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  -- Step 6: Since a > 0, a + 1 != 0, so a^2 - a - 1 = 0
  have h_quad_zero : a ^ 2 - a - 1 = 0 := by
    clear * - h_factored h₀
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
      (add norm 0 (by grind only [div_eq_one]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [mul_eq_zero]))
      (add norm 0 (by grind only [legendreSym.eq_zero_mod_of_eq_neg_one]))
      (add norm 0 (by grind only [zero_pow]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [div_eq_zero_iff]))
      (add norm 0 (by grind only [pow_eq_zero]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Quaternion.normSq_eq_zero]))
      (add norm 0 (by grind only [pow_eq_zero_iff]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [or_self_iff]))
      (add norm 0 (by grind only [div_ne_one]))
      (add norm 0 (by grind only [sq_eq_sq_iff_eq_or_eq_neg]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [mul_eq_one_iff']))
      (add norm 0 (by grind only [irrational_iff_ne_rational]))
      (add norm 0 (by grind only [sub_pow_char]))
      (add norm 0 (by grind only [integral_id]))
      (add norm 0 (by grind only [sub_pow_char_pow]))
      (add norm 0 (by grind only [Ideal.toCotangent_eq]))
      (add norm 0 (by grind only [OfNat.ofNat_ne_zero]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [pow_ne_zero]))
      (add unsafe 90% (by simp only [pow_two] at *))

  -- Step 7: a^2 = a + 1
  have h_a_sq_rel : a ^ 2 = a + 1 := by
    clear * - h_quad_zero
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableSimp := false
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
      (add norm 0 (by grind only [div_eq_one]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [integral_id]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [sq_eq_sq_iff_eq_or_eq_neg]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [IsCyclotomicExtension.Rat.Three.lambda_sq]))
      (add norm 0 (by grind only [FiniteField.pow_card_sub_one_eq_one]))
      (add norm 0 (by grind only [sub_pow_char_pow]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))

  -- Step 8: 1/a = a - 1
  have h_inv_a_rel : (1 / a : ℝ) = a - 1 := by
    clear * - h_a_sq_rel h₀
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [goldenConj]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [one_mul]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [mul_one]))
      (add norm 0 (by grind only [div_sub']))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [goldenRatio]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Real.sin_sq_eq_half_sub]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [sub_half]))
      (add norm 0 (by grind only [integral_id]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 1 (by apply div_mul))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))

  -- Step 9: a^3 = 2a + 1
  have h_a_pow_3 : a ^ 3 = 2 * a + 1 := by
    clear * - h_a_sq_rel
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Polynomial.derivative_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))

  -- Step 10: a^4 = 3a + 2
  have h_a_pow_4 : a ^ 4 = 3 * a + 2 := by
    clear * - h_a_pow_3 h_a_sq_rel
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
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
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [Polynomial.derivative_sq]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Real.sqrt_lt]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))

  -- Step 11: a^5 = 5a + 3
  have h_a_pow_5 : a ^ 5 = 5 * a + 3 := by
    clear * - h_a_pow_4 h_a_sq_rel
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
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Real.sqrt_lt]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
      (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))
      (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))

  -- Step 12: a^6 = 8a + 5
  have h_a_pow_6 : a ^ 6 = 8 * a + 5 := by
    clear * - h_a_pow_5 h_a_sq_rel
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
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by field_simp [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [Real.sqrt_lt]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [sq_sub_sq]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [euler_four_squares]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))

  -- Step 13: a^12 = (8a + 5)^2
  have h_a_pow_12_expand : a ^ 12 = (8 * a + 5) ^ 2 := by
    clear * - h_a_pow_6
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
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [pow_two_pow_sub_pow_two_pow]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [CharTwo.sum_sq]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [Quaternion.normSq_coe]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))

  -- Step 14: Expand square
  have h_a_pow_12_expanded : a ^ 12 = 64 * a ^ 2 + 80 * a + 25 := by
    clear * - h_a_pow_12_expand
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by field_simp [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [QuaternionGroup.xa_pow_four]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [sq_add_sq_mul_sq_add_sq]))
      (add norm 0 (by grind only [Polynomial.derivative_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [Int.sq_eq_one_of_sq_le_three]))
      (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))

  -- Step 15: Substitute a^2 = a + 1
  have h_a_pow_12_sub : a ^ 12 = 64 * (a + 1) + 80 * a + 25 := by
    clear * - h_a_pow_12_expanded h_a_sq_rel
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_y]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [ENNReal.rpow_two]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))

  -- Step 16: Simplify to 144a + 89
  have h_a_pow_12_simp : a ^ 12 = 144 * a + 89 := by
    clear * - h_a_pow_12_sub
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
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Polynomial.derivative_sq]))
      (add norm 0 (by grind only [Real.sqrt_lt]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [CoxeterSystem.IsReflection.pow_two]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
      (add unsafe 50% (by simp only [Int.sq_eq_one_of_sq_le_three]))
      (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))

  -- Step 17: Calculate LHS: a^12 - 144/a
  have h_lhs_calc : a ^ 12 - 144 * (1 / a : ℝ) = (144 * a + 89) - 144 * (a - 1) := by
    clear * - h_a_pow_12_simp h_inv_a_rel
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [div_sub']))
      (add norm 0 (by grind only [WeakFEPair.h_feq']))
      (add norm 0 (by grind only [one_div_one]))
      (add norm 0 (by grind only [sub_div']))
      (add norm 0 (by grind only [tsub_div]))
      (add norm 0 (by grind only [Real.rpow_sub]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [Real.sqrt_div_self']))
      (add norm 0 (by grind only [Real.sin_sq_eq_half_sub]))
      (add norm 0 (by grind only [goldenRatio]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [goldenConj]))
      (add norm 0 (by grind only [div_sub_div_same]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add norm 0 (by grind only [Real.rpow_sub']))
      (add norm 0 (by grind only [Real.div_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_one]))
      (add norm 0 (by grind only [Real.rpow_sub_one]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [div_mul] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [Real.div_rpow] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [div_right_comm] at *))

  -- Step 18: Final result 233
  have h_final : a ^ 12 - 144 * (1 / a : ℝ) = 233 := by
    clear * - h_lhs_calc
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
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [one_div_one]))
      (add norm 0 (by grind only [goldenRatio]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [one_half_pos]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 1 (by simp_all [one_div_lt]))
      (add norm 0 (by grind only [Real.one_rpow]))
      (add norm 0 (by grind only [div_sub']))
      (add norm 0 (by grind only [CircleDeg1Lift.transnumAuxSeq_dist_lt]))
      (add norm 0 (by grind only [Real.sqrt_one]))
      (add norm 0 (by grind only [Real.ofCauchy_one]))
      (add norm 0 (by grind only [goldenConj]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [WeakFEPair.h_feq']))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_apply_one]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [sub_half]))
      (add norm 0 (by grind only [Real.rpow_sub]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add unsafe 50% (by simp only [sq_sub_sq]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r1_pos]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [Real.log_lt_sub_one_of_pos]))

  exact h_final
