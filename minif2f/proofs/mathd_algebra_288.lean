
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

theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  -- Step 1: From h1 and h₀.y, we determine y = -6
  have h_y_eq_neg_6 : y = -6 := by
    clear * - h₁ h₀
    cases' abs_choice y with hy hy <;> linarith

  -- Step 2: Substitute y into the circle equation squared
  have h_circle_eq : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
    clear * - h₂
    rw [Real.sqrt_eq_iff_mul_self_eq, eq_comm] at h₂ <;> nlinarith

  -- Step 3: Substitute y = -6 into the circle equation
  have h_sub_y : (x - 8) ^ 2 + (-6 - 3) ^ 2 = 225 := by
    clear * - h_circle_eq h_y_eq_neg_6
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [neg_mul]))
      (add norm 0 (by grind only [neg_pow]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [add_sq]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [neg_eq]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [integral_id]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [Quaternion.mul_re]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [div_eq_mul_inv]))
      (add unsafe 50% (by nlinarith [mul_neg_one]))
      (add unsafe 50% (by nlinarith [neg_div]))
      (add unsafe 50% (by nlinarith [neg_one_mul]))
      (add unsafe 50% (by nlinarith [WeierstrassCurve.ψ_neg]))
      (add unsafe 50% (by nlinarith [inv_mul']))
      (add unsafe 50% (by nlinarith [Quaternion.mul_imJ]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imI]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imJ]))
      (add unsafe 50% (by nlinarith [Odd.neg_pow]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  -- Step 4: Simplify (-6 - 3)^2 to (-9)^2
  have h_neg_nine_sq : (-6 - 3 : ℝ) = -9 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
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
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [neg_div]))
      (add norm 0 (by grind only [div_neg]))
      (add norm 0 (by grind only [mul_neg]))
      (add norm 0 (by grind only [neg_mul]))
      (add norm 0 (by grind only [sub_half]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [neg_eq]))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Complex.ofReal_ofNat]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [Complex.cpow_neg_one]))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [div_mul] at *))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [mul_neg_one]))
      (add unsafe 50% (by nlinarith [neg_one_mul]))
      (add unsafe 50% (by nlinarith [div_eq_mul_inv]))
      (add unsafe 50% (by nlinarith [Complex.I_sq]))
      (add unsafe 50% (by nlinarith [Complex.arctan]))
      (add unsafe 50% (by nlinarith [Complex.I_mul_I]))
      (add unsafe 50% (by nlinarith [Real.arctan_neg]))

  have h_step4 : (x - 8) ^ 2 + (-9 : ℝ) ^ 2 = 225 := by
    clear * - h_sub_y h_neg_nine_sq
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
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
      (add safe 0 (by omega))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [neg_pow]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [Quaternion.sq_eq_neg_normSq]))
      (add norm 0 (by grind only [Quaternion.mul_re]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [neg_mul]))
      (add unsafe 50% (by nlinarith [mul_neg_one]))
      (add unsafe 50% (by nlinarith [neg_one_mul]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [mul_inv]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imI]))
      (add unsafe 50% (by nlinarith [Odd.neg_pow]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imJ]))
      (add unsafe 50% (by nlinarith [WeierstrassCurve.ψ_neg]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imI]))
      (add unsafe 50% (by nlinarith [Even.neg_pow]))
      (add unsafe 50% (by nlinarith [Odd.neg_one_pow]))
      (add unsafe 50% (by nlinarith [neg_eq]))
      (add unsafe 50% (by nlinarith [Quaternion.mul_imJ]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 50% (by nlinarith [QuaternionAlgebra.neg_imI]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imJ]))
      (add unsafe 50% (by nlinarith [neg_div]))

  -- Step 5: Calculate (-9)^2 = 81
  have h_ninety_one : (-9 : ℝ) ^ 2 = 81 := by
    clear * -
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
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [neg_pow]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [Odd.neg_one_pow]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
      (add norm 0 (by grind only [Derivation.leibniz_of_mul_eq_one]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [Int.units_sq]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Pell.Solution₁.prop]))
      (add unsafe 90% (by simp only [pow_two] at *))

  have h_step5 : (x - 8) ^ 2 + 81 = 225 := by
    clear * - h_step4 h_ninety_one
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
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [Nat.cast_ofNat]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [even_two_mul]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))

  -- Step 6: Subtract 81 from both sides
  have h_step6 : (x - 8) ^ 2 = 144 := by
    clear * - h_step5
    aesop (config := {
      maxRuleApplications := 100
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
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [integral_id]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [abs_sq]))
      (add unsafe 50% (by simp only [sq_sub_sq]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 50% (by simp only [euler_four_squares]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
      (add unsafe 90% (by simp only [ENNReal.rpow_two] at *))

  -- Step 7: Take square root implies absolute value
  have h_abs_diff : abs (x - 8) = 12 := by
    clear * - h_step6
    cases abs_cases (x - 8) <;> nlinarith

  -- Step 8: Split absolute value into cases
  have h_cases : x - 8 = 12 ∨ x - 8 = -12 := by
    clear * - h_abs_diff
    cases abs_cases (x - 8) <;> simp_all [-eq_comm]
    exact Or.inr (by linarith [abs_of_neg (by linarith : x - 8 < 0)])

  -- Step 9: Solve for x in both cases
  have h_x_cases : x = 20 ∨ x = -4 := by
    clear * - h_cases
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 600
      maxNormIterations := 320
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by gcongr))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 1 (by ring_nf at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [EuclideanGeometry.dist_div_sin_angle_of_angle_eq_pi_div_two]))
      (add safe 1 (by rw [EuclideanGeometry.dist_div_sin_oangle_left_of_oangle_eq_pi_div_two] at *))
      (add unsafe 10% (by grind only [Or]))
      (add unsafe 10% (by grind only [FiniteInter.finiteInterClosure_insert]))
      (add unsafe 10% (by grind only [Or.imp]))
      (add unsafe 10% (by grind only [Or.elim]))
      (add unsafe 10% (by grind only [Beatty.hit_or_miss']))
      (add unsafe 10% (by grind only [Or.imp_right]))
      (add unsafe 10% (by grind only [Or.symm]))
      (add unsafe 10% (by grind only [SimpleGraph.Walk.IsEulerian.card_filter_odd_degree]))
      (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_lt]))
      (add unsafe 10% (by grind only [Or.imp_left]))
      (add unsafe 10% (by grind only [Beatty.hit_or_miss]))
      (add unsafe 10% (by grind only [DirichletCharacter.even_or_odd]))
      (add unsafe 10% (by grind only [EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two]))
      (add unsafe 10% (by grind only [EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two]))
      (add unsafe 10% (by grind only [And]))
      (add unsafe 10% (by grind only [Or.intro_right]))
      (add unsafe 10% (by grind only [SzemerediRegularity.card_eq_of_mem_parts_chunk]))
      (add unsafe 10% (by grind only [or_not]))
      (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_gt]))
      (add unsafe 10% (by grind only [Or.intro_left]))
      (add unsafe 10% (by grind only [Ideal.IsPrime.mem_or_mem]))
      (add unsafe 10% (by grind only [IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd]))
      (add unsafe 10% (by grind only [ValuationSubring.mem_or_inv_mem]))
      (add unsafe 10% (by grind only [Ordnode.Raised]))
      (add unsafe 10% (by grind only [Nat.eq_zero_or_pos]))
      (add unsafe 10% (by grind only [Ordnode.pos_size_of_mem]))
      (add unsafe 10% (by grind only [Ordnode.size_balanceR]))
      (add unsafe 10% (by grind only [IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one]))
      (add unsafe 10% (by grind only [Compactum.join_distrib]))
      (add unsafe 10% (by grind only [Ideal.IsPrime.mem_pow_mul]))

  -- Step 10: Use x < 0 to select x = -4
  have h_x_eq_neg_4 : x = -4 := by
    clear * - h_x_cases h₀
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by field_simp [*] at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [lt_trichotomy]))
      (add norm 0 (by grind only [or_not]))
      (add norm 0 (by grind only [Real.log_neg_eq_log]))
      (add norm 0 (by grind only [Pell.Solution₁.y_neg]))
      (add norm 0 (by grind only [integral_rpow]))
      (add norm 0 (by grind only [Left.inv_lt_one_iff]))
      (add norm 0 (by grind only [Pell.Solution₁.y_inv]))
      (add norm 0 (by grind only [Pell.Solution₁.x_neg]))
      (add norm 0 (by grind only [Complex.arg_ofReal_of_neg]))
      (add norm 0 (by grind only [or_true]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_eq_or]))
      (add norm 0 (by grind only [EReal.neg_top]))
      (add norm 0 (by grind only [Right.inv_lt_one_iff]))
      (add norm 0 (by grind only [Real.sign_of_neg]))
      (add norm 0 (by grind only [EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two]))
      (add norm 0 (by grind only [EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two]))
      (add norm 0 (by grind only [or_self]))
      (add norm 0 (by grind only [Pell.Solution₁.ext]))
      (add norm 0 (by grind only [Left.one_lt_inv_iff]))
      (add norm 0 (by grind only [Pell.Solution₁.x_inv]))
      (add unsafe 10% (by grind only [Or]))
      (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_lt]))
      (add unsafe 10% (by grind only [FiniteInter.finiteInterClosure_insert]))
      (add unsafe 10% (by grind only [Or.elim]))
      (add unsafe 10% (by grind only [Or.imp]))
      (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_gt]))
      (add unsafe 10% (by grind only [ValuationSubring.mem_or_inv_mem]))
      (add unsafe 10% (by grind only [Beatty.hit_or_miss']))
      (add unsafe 10% (by grind only [SimpleGraph.Walk.IsEulerian.card_filter_odd_degree]))
      (add unsafe 10% (by grind only [DirichletCharacter.even_or_odd]))
      (add unsafe 10% (by grind only [And]))
      (add unsafe 10% (by grind only [Or.symm]))

  -- Step 11: Define relationship for n
  have h_n_def : x ^ 2 + y ^ 2 = (n : ℝ) := by
    clear * - h₃
    have hx := h₃
    rw [Real.sqrt_inj] at h₃
    · exact_mod_cast h₃
    · refine' add_nonneg (sq_nonneg x) (sq_nonneg y)
    · exact n.prop

  -- Step 12: Substitute x = -4 and y = -6
  have h_sub_vals : (-4 : ℝ) ^ 2 + (-6 : ℝ) ^ 2 = (n : ℝ) := by
    clear * - h_n_def h_x_eq_neg_4 h_y_eq_neg_6
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
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
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [neg_pow]))
      (add norm 0 (by grind only [neg_mul]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Derivation.leibniz_of_mul_eq_one]))
      (add norm 0 (by grind only [Quaternion.star_imI]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by rw [Quaternion.star_coe]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Nat.cast_ofNat]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [Complex.volume_ball]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Quaternion.coe_mul_eq_smul]))
      (add norm 0 (by grind only [Quaternion.star_mul_self]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [mul_neg_one]))
      (add unsafe 50% (by nlinarith [neg_one_mul]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imJ]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imI]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imK]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imJ]))
      (add unsafe 90% (by simp only [pow_two] at *))

  -- Step 13: Calculate squares
  have h_four_sq : (-4 : ℝ) ^ 2 = 16 := by
    clear * -
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
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [Derivation.leibniz_of_mul_eq_one]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [neg_pow]))
      (add norm 0 (by grind only [Int.units_sq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))

  have h_six_sq : (-6 : ℝ) ^ 2 = 36 := by
    clear * -
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
      (add norm 0 (by bound))
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
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [add_sq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Derivation.leibniz_of_mul_eq_one]))
      (add norm 0 (by grind only [even_two_mul]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [CoxeterSystem.IsReflection.pow_two]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))

  have h_step13 : 16 + 36 = (n : ℝ) := by
    clear * - h_sub_vals h_four_sq h_six_sq
    aesop (config := {
      maxRuleApplications := 1600
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
      (add norm 0 (by grind only [NNReal.coe_add]))
      (add norm 0 (by grind only [NNReal.coe_mul]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodySumFactor]))
      (add norm 0 (by rw [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Finset.mulETransformRight.card]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [NNReal.coe_two]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [add_tsub_cancel_of_le]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [ENNReal.add_halves]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodyLT'Factor]))
      (add norm 0 (by grind only [parallelogram_law_with_nnnorm]))
      (add norm 0 (by grind only [Real.coe_sqrt]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Real.sqrt]))

  -- Step 14: Sum the values
  have h_sum : 16 + 36 = 52 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [sub_half]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [zpow_two]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [add_halves']))
      (add norm 0 (by grind only [Real.Angle.two_nsmul_toReal_eq_two_mul_add_two_pi]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self']))
      (add norm 0 (by grind only [Real.Angle.two_nsmul_toReal_eq_two_mul_sub_two_pi]))
      (add norm 0 (by grind only [Real.Angle]))
      (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [Real.Angle.two_nsmul_toReal_eq_two_mul]))
      (add norm 0 (by grind only [Ring.multichoose_two]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [half_sub]))
      (add norm 0 (by grind only [Real.Angle.toReal_coe_eq_self_add_two_pi_iff]))

  have h_step14 : (n : ℝ) = 52 := by
    clear * - h_step13 h_sum
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.coe_sqrt]))
      (add norm 0 (by grind only [NNReal.coe_rpow]))
      (add norm 0 (by grind only [NNReal.coe_inj]))
      (add norm 0 (by grind only [NNReal.val_eq_coe]))
      (add norm 0 (by grind only [ENNReal.coe_inj]))
      (add norm 0 (by grind only [NNReal.sqrt]))
      (add norm 0 (by grind only [NNReal.coe_mul]))
      (add norm 0 (by grind only [NNReal.sqrt_eq_rpow]))
      (add norm 0 (by grind only [NNReal.coe_pow]))
      (add norm 0 (by grind only [norm_algebraMap_nnreal]))
      (add norm 0 (by grind only [NNReal.coe_real_pi]))
      (add norm 0 (by grind only [NNReal.sq_sqrt]))
      (add norm 0 (by grind only [NNReal.sqrt_sq]))
      (add norm 0 (by grind only [Real.toNNReal_coe]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodyLTFactor]))
      (add norm 0 (by grind only [NNReal.coe_mk]))
      (add norm 0 (by grind only [NNReal.norm_eq]))
      (add norm 0 (by grind only [NNReal.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [NNReal.isConjExponent_coe]))
      (add norm 0 (by grind only [NNReal.coe_zero]))
      (add norm 0 (by grind only [Quaternion.nnnorm_coe]))
      (add norm 0 (by grind only [ENNReal.coe_pow]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodyLT'Factor]))
      (add norm 0 (by grind only [ENNReal.coe_ofNat]))
      (add norm 0 (by grind only [NNReal.coe_ofNat]))
      (add norm 0 (by grind only [NNReal.mul_rpow]))
      (add norm 0 (by grind only [NNReal.coe_add]))
      (add norm 0 (by grind only [norm_toNNReal']))
      (add norm 0 (by grind only [NNReal.sqrt_inv]))
      (add norm 0 (by grind only [NNReal.pi]))
      (add norm 0 (by grind only [nnnorm_algebraMap_nnreal]))

  -- Step 15: Conclude n = 52
  have h_final : n = 52 := by
    clear * - h_step14
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.coe_sqrt]))
      (add norm 0 (by grind only [NNReal.coe_rpow]))
      (add norm 0 (by grind only [NNReal.coe_inj]))
      (add norm 0 (by grind only [NNReal.coe_pow]))
      (add norm 0 (by grind only [NNReal.sqrt]))
      (add norm 0 (by grind only [NNReal.val_eq_coe]))
      (add norm 0 (by grind only [NNReal.sqrt_eq_rpow]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodyLTFactor]))
      (add norm 0 (by grind only [ENNReal.coe_inj]))
      (add norm 0 (by grind only [NNReal.norm_eq]))
      (add norm 0 (by grind only [NNReal.sq_sqrt]))
      (add norm 0 (by grind only [ENNReal.coe_pow]))
      (add norm 0 (by grind only [NNReal.coe_mul]))
      (add norm 0 (by grind only [NNReal.sqrt_sq]))
      (add norm 0 (by grind only [norm_algebraMap_nnreal]))
      (add norm 0 (by grind only [NNReal.isConjExponent_coe]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [NNReal.coe_real_pi]))
      (add norm 0 (by grind only [Real.toNNReal_coe]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodyLT'Factor]))
      (add norm 0 (by grind only [NNReal.coe_zero]))
      (add norm 0 (by grind only [NNReal.coe_mk]))
      (add norm 0 (by grind only [NNReal.mul_rpow]))
      (add norm 0 (by grind only [NNReal.rpow_natCast]))
      (add norm 0 (by grind only [NNReal.sqrt_mul]))
      (add norm 0 (by grind only [NNReal.coe_ofNat]))
      (add norm 0 (by grind only [norm_toNNReal']))
      (add norm 0 (by grind only [Quaternion.nnnorm_coe]))
      (add norm 0 (by grind only [NNReal.sqrt_inv]))
      (add norm 0 (by grind only [NNReal.coe_inv]))
      (add norm 0 (by grind only [ENNReal.coe_natCast]))
      (add norm 0 (by grind only [ENNReal.coe_rpow_of_nonneg]))

  exact h_final
