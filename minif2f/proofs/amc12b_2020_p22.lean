
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

theorem amc12b_2020_p22 :
    IsGreatest
      { ((2^t - 3 * t) * t) / (4^t) | (t : ℝ)}
      (1 / 12) := by
  -- Define the function f(t)
  let f : ℝ → ℝ := fun t => ((2^t - 3 * t) * t) / (4^t)
  -- Step 1 & 2 & 3: Rewrite f(t) in terms of u = t / 2^t
  have h_step3_form : ∀ t, f t = (t / (2:ℝ)^t) - 3 * (t / (2:ℝ)^t)^2 := by
    clear * -
    simp [f, div_eq_mul_inv, mul_assoc]
    intro ε
    ring_nf
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num)]
    · ring_nf <;> field_simp [Real.rpow_def_of_pos] <;> ring
    · norm_num

  -- Define u(t) = t / 2^t
  let u : ℝ → ℝ := fun t => t / (2:ℝ)^t
  -- Step 4: Relate f to u
  have h_f_in_u : ∀ t, f t = u t - 3 * (u t)^2 := by
    clear * - h_step3_form
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 600
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [CircleDeg1Lift.transnumAuxSeq]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [mul_div_right_comm]))
      (add norm 0 (by grind only [tsub_div]))
      (add norm 0 (by grind only [Real.cos_sq]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Real.sin_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [CircleDeg1Lift.transnumAuxSeq_def]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 1 (by apply div_mul))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [div_right_comm] at *))
      (add safe 0 (by simp only [norm_div] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))

  -- Step 5: Define y(u) = u - 3u^2
  let y : ℝ → ℝ := fun v => v - 3 * v^2
  -- Step 6: Complete the square for y(u)
  have h_y_complete_square : ∀ v, y v = -3 * (v - 1/6)^2 + 1/12 := by
    clear * -
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
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [integral_id]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [integral_gaussian]))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [ProbabilityTheory.variance_def']))
      (add norm 0 (by grind only [ENNReal.rpow_two]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  -- Step 7: Establish that y(v) <= 1/12
  have h_y_max : ∀ v, y v ≤ 1/12 := by
    clear * - h_y_complete_square
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
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
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [NumberField.abs_discr_ge]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [one_le_two]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [div_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [Bertrand.real_main_inequality]))

  -- Step 8: The maximum occurs when u = 1/6
  -- We need to show there exists a t such that u t = 1/6
  -- Step 9, 10, 11: This is equivalent to 2^t - 6t = 0
  let g : ℝ → ℝ := fun t => (2:ℝ)^t - 6 * t
  -- Step 12: Define g(t)
  -- Step 13 & 14: Evaluate g at 0 and 1
  have h_g_0 : g 0 = 1 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
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
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [zero_pow]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [integral_id]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [zero_div]))
      (add norm 0 (by grind only [ENNReal.two_ne_top]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [zero_le_two]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 90% (by simp only [ENNReal.rpow_two] at *))
      (add unsafe 90% (by simp only [Complex.cpow_two] at *))

  have h_g_1 : g 1 = -4 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
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
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [ENNReal.two_ne_top]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [Cardinal.lift_two]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [one_lt_two]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 90% (by simp only [ENNReal.rpow_two] at *))

  -- Step 15: Intermediate Value Theorem application setup
  have h_ivt_cond : ContinuousOn g (Set.Icc 0 1) := by
    clear * -
    fun_prop (disch := norm_num)

  have h_sign_change : g 0 * g 1 < 0 := by
    clear * - h_g_0 h_g_1
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 256
      enableSimp := false
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
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.x_mul_pos]))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.y_mul]))
      (add unsafe 50% (by nlinarith [inv_lt_inv]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_logb]))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.y_mul_pos]))
      (add unsafe 50% (by nlinarith [inv_lt_one]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_logb_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_right]))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.x_mul]))
      (add unsafe 50% (by nlinarith [Real.rpow_lt_rpow_of_exponent_gt]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_neg_left]))
      (add unsafe 50% (by nlinarith [mul_neg_of_neg_of_pos]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [mul_neg_of_pos_of_neg]))
      (add unsafe 50% (by nlinarith [Real.logb_neg]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [lt_mul_of_le_of_one_lt]))
      (add unsafe 50% (by nlinarith [inv_lt_iff_one_lt_mul]))
      (add unsafe 50% (by nlinarith [lt_inv]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_le_of_lt]))
      (add unsafe 50% (by nlinarith [inv_lt_iff_one_lt_mul']))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_right']))
      (add unsafe 50% (by nlinarith [Real.log_neg]))

  -- Step 16: There exists t0 in (0,1) such that g(t0) = 0, i.e., u(t0) = 1/6
  -- Using IVT, there exists c in (0,1) such that g c = 0
  obtain ⟨t0, ht0⟩ : ∃ t0 ∈ Set.Ioo (0:ℝ) (1:ℝ), g t0 = 0 := by
    -- Standard IVT lemma usage would go here, but we just assert existence based on previous steps
    apply intermediate_value_Ioo' <;> aesop

  -- From g t0 = 0, we have 2^t0 = 6*t0, so t0/2^t0 = 1/6
  have h_u_t0 : u t0 = 1/6 := by
    have h_gt0_zero : g t0 = 0 := ht0.2
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
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
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [mul_div_cancel₀]))
      (add norm 0 (by grind only [LT.lt.ne']))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [pow_pos]))
      (add norm 0 (by grind only [integral_id]))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [Iff]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_pos]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [neg_div]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by nlinarith [Real.pi_pos]))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 10% (by grind only [ne_of_gt]))
      (add unsafe 50% (by simp only [sq_sub_sq]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [one_half_pos]))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [Real.rpow_pos_of_pos]))
      (add unsafe 50% (by nlinarith [inv_pos]))

  -- Step 17: Max value is 1/12
  -- First part: Show 1/12 is an upper bound
  have h_upper_bound : ∀ t, f t ≤ 1/12 := by
    intro t
    have h_f_val : f t = y (u t) := by
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        maxGoals := 512
        enableSimp := false
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 1 (by push_neg))
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
        (add norm 0 (by grind only [div_pow]))
        (add norm 0 (by grind only [two_ne_zero]))
        (add norm 0 (by grind only [two_ne_zero']))
        (add norm 0 (by grind only [sq_pos_of_pos]))
        (add norm 0 (by grind only [mul_pow]))
        (add norm 0 (by grind only [one_div]))
        (add norm 0 (by grind only [mul_le_mul_left]))
        (add norm 0 (by grind only [zero_lt_two]))
        (add norm 0 (by grind only [integral_id]))
        (add norm 0 (by grind only [Real.sq_sqrt]))
        (add norm 0 (by grind only [Real.sin_sq]))
        (add norm 0 (by grind only [mabs_of_one_lt]))
        (add norm 0 (by grind only [zero_le_two]))
        (add norm 0 (by grind only [sq_abs]))
        (add norm 0 (by grind only [sub_sq]))
        (add norm 0 (by grind only [mul_le_mul_right]))
        (add norm 0 (by grind only [sq_nonneg]))
        (add norm 0 (by grind only [mul_div_cancel_left]))
        (add norm 0 (by grind only [sq_lt_sq]))
        (add safe 0 (by simp only [div_self] at *))
        (add safe 0 (by simp only [mul_div_cancel₀] at *))
        (add safe 0 (by simp only [mul_div_assoc] at *))
        (add safe 0 (by simp only [div_div] at *))
        (add safe 0 (by simp only [div_mul_cancel₀] at *))
        (add safe 0 (by simp only [mul_div] at *))
        (add safe 0 (by simp only [sub_div] at *))
        (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
        (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
        (add safe 0 (by nlinarith [Real.pi_pos]))
        (add safe 1 (by apply div_mul))
        (add unsafe 50% (by simp only [sq_sub_sq]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_left]))

    have h_y_bound : y (u t) ≤ 1/12 := by
      apply h_y_max

    calc
      f t = y (u t) := by rw [h_f_val]
      _ ≤ 1/12 := by apply h_y_bound

  -- Second part: Show 1/12 is attained
  have h_attained : ∃ t, f t = 1/12 := by
    use t0
    have h_u_val : u t0 = 1/6 := h_u_t0
    have h_y_val : y (u t0) = 1/12 := by
      rw [h_y_complete_square]; rw [h_u_val]; norm_num

    calc
      f t0 = y (u t0) := by rw [h_f_in_u]
      _ = 1/12 := by exact h_y_val

  -- Construct the IsGreatest proof
  -- refine' ⟨h_upper_bound, h_attained⟩
  aesop  (add simp [IsGreatest, upperBounds, lowerBounds])
