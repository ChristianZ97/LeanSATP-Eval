
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

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  -- Step 1: Expand square of sum
  have h_sum_sq : (a + b + c)^2 = a^2 + b^2 + c^2 + 2*(a*b + b*c + c*a) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [sq_add_sq_mul_sq_add_sq]))
      (add norm 0 (by grind only [sq_add_mul_sq_mul_sq_add_mul_sq]))
      (add norm 0 (by grind only [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [norm_add_sq_real]))
      (add norm 0 (by rw [Quaternion.coe_mul]))
      (add norm 0 (by grind only [sum_eight_sq_mul_sum_eight_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
      (add norm 0 (by grind only [Quaternion.star_mul_self]))
      (add norm 0 (by grind only [sum_four_sq_mul_sum_four_sq]))
      (add norm 0 (by grind only [Quaternion.normSq_coe]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Quaternion.coe_mul_eq_smul]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [add_sq]))
      (add norm 0 (by grind only [norm_add_sq]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [aux_add]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Quaternion.inner_self]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_y]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by rw [Quaternion.star_coe]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 90% (by simp only [pow_two] at *))

  -- Step 2: Substitute known values into expansion
  have h_subst : 2^2 = a^2 + b^2 + c^2 + 2*(1) := by
    clear * - h_sum_sq h₁ h₂
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
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_self]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [Nat.cast_ofNat]))
      (add norm 0 (by grind only [AddChar.mulShift_apply]))
      (add norm 0 (by grind only [one_pow]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))

  -- Step 3: Calculate sum of squares
  have h_sq_sum : a^2 + b^2 + c^2 = 2 := by
    clear * - h_subst
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      maxGoals := 256
      enableSimp := false
      enableUnfold := false
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
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 90% (by simp only [Nat.cast_two] at *))
      (add unsafe 90% (by simp only [ENNReal.rpow_two] at *))
      (add unsafe 90% (by simp only [NNReal.rpow_two] at *))
      (add unsafe 90% (by simp only [sq_eq_one_iff] at *))
      (add unsafe 90% (by simp only [Complex.cpow_two] at *))

  -- Step 4: Define polynomial P(x) whose roots are a, b, c
  let P : ℝ → ℝ := fun x => x^3 - (a + b + c)*x^2 + (a*b + b*c + c*a)*x - a*b*c

  -- Step 5: Simplify polynomial coefficients
  have h_P_def : ∀ x, P x = x^3 - 2*x^2 + x - a*b*c := by
    clear * - h₁ h₂
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 600
      maxNormIterations := 320
      enableUnfold := false
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
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Quaternion.coe_re]))
      (add norm 0 (by grind only [HurwitzKernelBounds.f_nat]))
      (add norm 0 (by grind only [Pell.Solution₁.y_mul]))
      (add norm 0 (by grind only [forall_const]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [mul_lt_mul_iff_left]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [sub_one_lt]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Real.sqrt_lt]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Pell.Solution₁.x_mul]))
      (add norm 0 (by grind only [Quaternion.star_re]))
      (add norm 0 (by grind only [Quaternion.sub_re]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [Real.pi_pos]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_tsum]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
      (add unsafe 90% (by simp only [pow_two] at *))

  -- Step 6: Factor polynomial structure
  have h_P_factor : ∀ x, P x = x*(x - 1)^2 - a*b*c := by
    clear * - h_P_def
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
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
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [sum_four_sq_mul_sum_four_sq]))
      (add norm 0 (by grind only [sum_eight_sq_mul_sum_eight_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [Quaternion.normSq_def']))
      (add norm 0 (by rw [Quaternion.coe_mul]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [Quaternion.normSq_coe]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Quaternion.normSq_ratCast]))
      (add norm 0 (by grind only [Quaternion.star_mul_self]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Quaternion.normSq]))
      (add norm 0 (by grind only [Quaternion.star_mul_eq_coe]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [norm_add_sq_real]))
      (add norm 0 (by grind only [RCLike.normSq_eq_def']))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [Quaternion.self_mul_star]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [Quaternion.normSq_natCast]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_x]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))

  -- Step 7: Derivative of P(x) ignoring constant abc
  let dP_no_c : ℝ → ℝ := fun x => 3*x^2 - 4*x + 1

  -- Step 8: Factor derivative
  have h_deriv_factor : ∀ x, dP_no_c x = (3*x - 1)*(x - 1) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 600
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 100 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Stirling.stirlingSeq]))
      (add norm 0 (by grind only [forall_const]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [funext]))
      (add norm 0 (by grind only [groupCohomology.dZero]))
      (add norm 0 (by grind only [rfl]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [groupCohomology.dOne]))
      (add norm 0 (by grind only [groupCohomology.dTwo]))
      (add norm 0 (by grind only [Real.deriv_arccos]))
      (add norm 0 (by grind only [Real.GammaSeq]))
      (add norm 0 (by grind only [deriv_tsum]))
      (add norm 0 (by grind only [Function.funext_iff]))
      (add norm 0 (by grind only [HurwitzKernelBounds.F_nat]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_tsum]))
      (add norm 0 (by grind only [discrim]))
      (add norm 0 (by grind only [DirichletCharacter.LSeries_twist_vonMangoldt_eq]))
      (add norm 0 (by grind only [Turing.TM0.Cfg]))
      (add norm 0 (by grind only [Derivation.sub_apply]))
      (add norm 0 (by grind only [deriv_tsum_apply]))
      (add norm 0 (by grind only [forall_true_iff]))
      (add norm 0 (by grind only [Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]))
      (add norm 0 (by grind only [Real.deriv_tan_sub_id]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [div_mul]))
      (add norm 0 (by grind only [Nat.recOnMul]))
      (add norm 0 (by grind only [ClassGroup.cardM]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [congr]))
      (add norm 0 (by grind only [ArithmeticFunction.ext_iff]))
      (add norm 0 (by grind only [deriv_pow]))
      (add norm 0 (by grind only [CircleDeg1Lift.transnumAuxSeq]))

  -- Step 9: Critical points of the variable part
  have h_crit_pts : {x : ℝ | dP_no_c x = 0} = {(1:ℝ)/3, 1} := by
    clear * - h_deriv_factor
    aesop  (add simp [Set.ext_iff])
    ·
      exact
        Or.inl <| by
          apply eq_inv_of_mul_eq_one_left
          linarith
    · exact .inr <| by linarith [h_1]

  -- Step 10: Evaluate P at x = 1/3
  have h_P_at_1_3 : P ((1:ℝ)/3) = 4 / 27 - a*b*c := by
    clear * - h_P_factor
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      maxGoals := 512
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.pi]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [gosperCatalan]))
      (add norm 0 (by grind only [CircleDeg1Lift.transnumAuxSeq]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [Complex.arctan] at *))
      (add safe 0 (by simp only [div_mul] at *))
      (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add unsafe 50% (by nlinarith [Real.arctan_ne_mul_pi_div_two]))

  -- Step 11: Evaluate P at x = 1
  have h_P_at_1 : P 1 = 0 - a*b*c := by
    clear * - h_P_factor
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by norm_cast))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [one_ne_zero]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [IsLprojection.coe_compl]))
      (add norm 0 (by grind only [ArithmeticFunction.natCoe_one]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_apply_one]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [Real.Gamma_one]))
      (add norm 0 (by grind only [Polynomial.derivative_one]))
      (add norm 0 (by rw [Quaternion.coe_one]))
      (add norm 0 (by grind only [ArithmeticFunction.one_one]))
      (add norm 0 (by grind only [ArithmeticFunction.one_apply]))
      (add norm 0 (by grind only [Nat.factorial_one]))
      (add norm 0 (by grind only [Real.one_rpow]))
      (add norm 0 (by grind only [Polynomial.content_one]))
      (add norm 0 (by grind only [integral_one]))
      (add norm 0 (by grind only [Real.rpow_zero]))
      (add norm 0 (by grind only [Polynomial.eval_one]))
      (add norm 0 (by grind only [Polynomial.Chebyshev.U_one]))
      (add norm 0 (by grind only [ArithmeticFunction.convolution_vonMangoldt_const_one]))
      (add norm 0 (by rw [LSeries.one_convolution_eq_zeta_convolution]))
      (add norm 0 (by grind only [Real.log_one]))
      (add norm 0 (by grind only [IsLprojection.coe_one]))
      (add norm 0 (by grind only [HahnSeries.C_one]))
      (add norm 0 (by grind only [PowerSeries.coe_one]))
      (add norm 0 (by grind only [ArithmeticFunction.vonMangoldt_apply_one]))
      (add norm 0 (by grind only [ArithmeticFunction.one_eq_delta]))
      (add norm 0 (by grind only [gronwallBound_ε0]))
      (add norm 0 (by grind only [Polynomial.coe_one]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [RatFunc.denom_one]))

  -- Step 12: Bounds on abc derived from P(roots)=0 and monotonicity arguments
  -- Since a,b,c are roots, P(a)=P(b)=P(c)=0. 
  -- The local max at 1/3 must be >= 0 and local min at 1 must be <= 0.
  have h_abc_bounds : 0 ≤ a*b*c ∧ a*b*c ≤ 4 / 27 := by
    clear * - h_P_at_1_3 h_P_at_1 h₀ h₁ h₂
    have hc : c = 2 - a - b := by linarith
    simp_all [mul_assoc]
    constructor
    · nlinarith [sq_nonneg (b - (2 - a - b)), sq_nonneg a]
    · nlinarith [sq_nonneg (a - 2 / 3), sq_nonneg (b - 2 / 3), mul_self_nonneg (a + b - 2 / 3), mul_self_nonneg (a - b)]

  -- Step 13: Analyze factorization for lower bound case abc=0
  -- If abc=0, one root is 0. Given ordering a<=b<=c, a=0.
  -- Roots of x(x-1)^2 are 0, 1, 1. So a=0, b=1, c=1 satisfies bounds.

  -- Step 14: Analyze factorization for upper bound case abc=4/27
  -- If abc=4/27, roots are related to critical point values.

  -- Step 15: Lower bound for a
  have h_a_ge_0 : 0 ≤ a := by
    clear * - h_abc_bounds h₀ h₁ h₂
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
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
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [unitInterval.nonneg]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [one_le_div']))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [unitInterval.le_one]))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 50% (by nlinarith [mul_le_one]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [div_le_one_of_le]))
      (add unsafe 50% (by nlinarith [CircleDeg1Lift.le_translationNumber_of_add_le]))

  -- Step 16: Upper bound for a
  have h_a_le_1_3 : a ≤ 1 / 3 := by
    clear * - h_abc_bounds h₀ h₁ h₂ h_a_ge_0
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [sq_le]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [mul_le_one]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [div_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [Int.cast_one_le_of_pos]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))
      (add unsafe 50% (by nlinarith [unitInterval.le_one]))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [Real.logb_le_logb]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [inv_le_div_iff_le_mul]))

  -- Step 17: Lower bound for b
  have h_b_ge_1_3 : 1 / 3 ≤ b := by
    clear * - h_abc_bounds h₀ h₁ h₂ h_a_le_1_3
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [div_le_inv_mul_iff]))
      (add norm 0 (by grind only [Real.sqrt_one_add_le]))
      (add norm 0 (by grind only [sq_le]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [inv_le_div_iff_le_mul]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [inv_le_inv]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_right]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [mul_inv_le_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))

  -- Step 18: Upper bound for b
  have h_b_le_1 : b ≤ 1 := by
    clear * - h_abc_bounds h₀ h₁ h₂ h_b_ge_1_3
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.exp_le_one_iff]))
      (add norm 0 (by grind only [div_le_one']))
      (add norm 0 (by grind only [div_le_self_iff]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [one_le_div']))
      (add unsafe 50% (by nlinarith [mul_le_one]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [unitInterval.le_one]))
      (add unsafe 50% (by nlinarith [Int.cast_one_le_of_pos]))
      (add unsafe 50% (by nlinarith [one_le_mul_of_one_le_of_one_le]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [div_le_one_of_le]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_right']))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_left']))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r_lower_bound_on_verticalStrip]))
      (add unsafe 50% (by nlinarith [Int.le_add_one]))
      (add unsafe 50% (by nlinarith [one_le_leOnePart]))
      (add unsafe 50% (by nlinarith [Real.logb_le_logb]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [Real.log_nonpos]))
      (add unsafe 50% (by nlinarith [CircleDeg1Lift.le_translationNumber_of_add_le]))
      (add unsafe 50% (by nlinarith [Real.logb_nonpos]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [le_mul_of_le_of_one_le]))

  -- Step 19: Lower bound for c
  have h_c_ge_1 : 1 ≤ c := by
    clear * - h_abc_bounds h₀ h₁ h₂ h_b_le_1
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
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
      (add norm 0 (by grind only [le_mul_iff_one_le_left']))
      (add norm 0 (by grind only [le_mul_iff_one_le_right']))
      (add norm 0 (by grind only [one_le_leOnePart]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [div_le_self_iff]))
      (add norm 0 (by grind only [div_le_one']))
      (add norm 0 (by grind only [zero_le_one]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [Real.exp_le_one_iff]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [Int.le_add_one]))
      (add norm 0 (by grind only [one_le_oneLePart]))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [sq_le_one_iff]))
      (add unsafe 90% (by simp only [le_mul_of_one_le_right'] at *))
      (add unsafe 90% (by simp only [le_mul_of_one_le_left'] at *))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 90% (by simp only [unitInterval.le_one] at *))
      (add unsafe 50% (by nlinarith [mul_le_one]))
      (add unsafe 50% (by nlinarith [one_le_mul_of_one_le_of_one_le]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_le_of_one_le]))
      (add unsafe 50% (by nlinarith [Int.cast_one_le_of_pos]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [CircleDeg1Lift.le_translationNumber_of_add_le]))
      (add unsafe 50% (by nlinarith [Real.log_nonneg_iff]))

  -- Step 20: Upper bound for c
  have h_c_le_4_3 : c ≤ 4 / 3 := by
    clear * - h_abc_bounds h₀ h₁ h₂ h_c_ge_1
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [sq_le]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [div_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le']))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_div_iff_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [Behrend.two_div_one_sub_two_div_e_le_eight]))

  -- Combine all inequalities
  have h_final : 0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
    clear * - h_a_ge_0 h_a_le_1_3 h_b_ge_1_3 h_b_le_1 h_c_ge_1 h_c_le_4_3
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [div_le_one']))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [le_mul_iff_one_le_right']))
      (add norm 0 (by grind only [le_mul_iff_one_le_left']))
      (add norm 0 (by grind only [div_le_self_iff]))
      (add norm 0 (by grind only [CircleDeg1Lift.le_translationNumber_of_add_le]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [Real.rpow_le_rpow]))
      (add norm 0 (by grind only [one_le_leOnePart]))
      (add norm 0 (by grind only [Real.log_nonneg]))
      (add norm 0 (by grind only [abs_le]))
      (add norm 0 (by grind only [Real.arcsin_nonneg]))
      (add norm 0 (by grind only [Real.log_nonpos]))
      (add norm 0 (by grind only [one_le_oneLePart]))
      (add norm 0 (by grind only [Complex.real_le_real]))
      (add norm 0 (by grind only [Real.two_div_pi_mul_le_sin]))
      (add norm 0 (by grind only [inv_le']))
      (add norm 0 (by grind only [unitInterval.nonneg]))
      (add unsafe 10% (by grind only [EisensteinSeries.r_lower_bound_on_verticalStrip]))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 10% (by grind only [zero_le_one]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 90% (by simp only [le_mul_of_one_le_right'] at *))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 10% (by grind only [le_of_lt]))
      (add unsafe 50% (by nlinarith [unitInterval.le_one]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))

  exact h_final
