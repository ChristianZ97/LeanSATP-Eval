
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

theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h1_pos_xy : 0 < x + y := by
    clear * - h₀
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
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by nlinarith [Real.mul_pos]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_exp]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_one_iff]))
      (add unsafe 50% (by nlinarith [Real.b_pos]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [zero_lt_one]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r1_pos]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [Real.rpow_lt_rpow]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_right']))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left]))
      (add unsafe 50% (by nlinarith [Behrend.exp_neg_two_mul_le]))
      (add unsafe 50% (by nlinarith [inv_pos]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_right]))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.x_mul_pos]))
      (add unsafe 50% (by nlinarith [div_lt_one]))
      (add unsafe 50% (by nlinarith [inv_lt_one]))
      (add unsafe 50% (by nlinarith [inv_lt_inv]))
      (add unsafe 50% (by nlinarith [Real.rpow_pos_of_pos]))
      (add unsafe 50% (by nlinarith [pow_lt_one]))
      (add unsafe 50% (by nlinarith [Real.log_neg]))
      (add unsafe 50% (by nlinarith [lt_inv]))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_right]))
      (add unsafe 50% (by nlinarith [Real.rpow_def_of_pos]))
      (add unsafe 50% (by nlinarith [Real.log_lt_iff_lt_exp]))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [Real.log_pos]))
      (add unsafe 50% (by nlinarith [Real.log_lt_log_iff]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))

  have h2_pos_yz : 0 < y + z := by
    clear * - h₀
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
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add safe 0 (by nlinarith [Real.pi_div_two_pos]))
      (add unsafe 50% (by nlinarith [Real.mul_pos]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [Real.exp_lt_exp]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [div_lt_one]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left]))
      (add unsafe 50% (by nlinarith [Behrend.exp_neg_two_mul_le]))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_right]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [Real.b_pos]))
      (add unsafe 50% (by nlinarith [div_lt_iff']))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r1_pos]))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_right]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_one_iff]))
      (add unsafe 50% (by nlinarith [lt_div_iff']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [Real.aux₀]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_right']))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.x_mul_pos]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
      (add unsafe 50% (by nlinarith [one_lt_div]))
      (add unsafe 50% (by nlinarith [Real.add_lt_add_iff_left]))
      (add unsafe 50% (by nlinarith [Real.log_lt_iff_lt_exp]))
      (add unsafe 50% (by nlinarith [div_lt_self_iff]))
      (add unsafe 50% (by nlinarith [pow_lt_one]))

  have h3_pos_zx : 0 < z + x := by
    clear * - h₀
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
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
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
      (add safe 0 (by nlinarith [Real.pi_div_two_pos]))
      (add unsafe 50% (by nlinarith [Real.mul_pos]))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_right]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [div_lt_one]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.x_mul_pos]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_right]))
      (add unsafe 50% (by nlinarith [one_lt_div]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r1_pos]))
      (add unsafe 50% (by nlinarith [Real.b_pos]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [div_lt_iff']))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [Real.sqrt_pos]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_right']))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.y_mul_pos]))
      (add unsafe 50% (by nlinarith [Real.aux₀]))
      (add unsafe 50% (by nlinarith [lt_div_iff']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_one_iff]))
      (add unsafe 50% (by nlinarith [mul_self_pos]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_exp]))
      (add unsafe 50% (by nlinarith [pow_lt_one]))
      (add unsafe 50% (by nlinarith [zero_lt_one]))

  have h4_sum_xy_yz_zx : (x + y) + (y + z) + (z + x) = 2 * (x + y + z) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 512
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
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Ring.multichoose_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
      (add norm 0 (by grind only [zpow_two]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self']))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star']))
      (add norm 0 (by grind only [Nat.fib_two_mul]))
      (add norm 0 (by grind only [parallelogram_law]))
      (add norm 0 (by grind only [Complex.sin_two_mul]))

  -- Applying Cauchy-Schwarz inequality (Titu's Lemma form or standard AM-HM via Cauchy)
    -- ((x+y)+(y+z)+(z+x)) * (1/(x+y) + 1/(y+z) + 1/(z+x)) >= (1+1+1)^2

  have h5_cauuchy_schwarz : 
      ((x + y) + (y + z) + (z + x)) * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ (1 + 1 + 1 : ℝ) ^ 2 := by
    clear * - h1_pos_xy h2_pos_yz h3_pos_zx
    field_simp [add_comm, add_left_comm, add_assoc]
    nlinarith [sq_nonneg (x - y), sq_nonneg (z - x), sq_nonneg (y - z)]

  have h6_substitute_sum : 
      2 * (x + y + z) * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ (1 + 1 + 1 : ℝ) ^ 2 := by
    clear * - h4_sum_xy_yz_zx h5_cauuchy_schwarz
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 16
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
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 0 (by grind only [pow_le_pow_left]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 90% (by simp only [le_mul_of_one_le_right'] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 90% (by simp only [one_le_two] at *))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_right']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_left']))
      (add unsafe 50% (by nlinarith [le_trans]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [one_add_mul_le_pow]))
      (add unsafe 50% (by nlinarith [Real.BohrMollerup.f_add_nat_ge]))

  have h7_nine_rhs : (1 + 1 + 1 : ℝ) ^ 2 = 9 := by
    clear * -
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
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [CoxeterSystem.IsReflection.pow_two]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [Pell.Solution₁.prop]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))
      (add norm 0 (by grind only [add_sq]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add unsafe 90% (by simp only [pow_two] at *))

  have h8_substitute_nine : 
      2 * (x + y + z) * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 9 := by
    clear * - h6_substitute_sum h7_nine_rhs
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
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
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [pow_le_pow_left]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add unsafe 90% (by simp only [le_mul_of_one_le_right'] at *))
      (add unsafe 90% (by simp only [le_mul_of_one_le_left'] at *))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_right']))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_left']))
      (add unsafe 90% (by simp only [one_le_two] at *))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [SzemerediRegularity.hundred_le_m]))
      (add unsafe 50% (by nlinarith [one_le_pow_of_one_le]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [le_div_iff]))

  have h9_pos_xyz : 0 < x + y + z := by
    clear * - h₀
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
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
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
      (add norm 0 (by grind only [mul_neg_of_neg_of_pos]))
      (add safe 0 (by nlinarith [Real.pi_div_two_pos]))
      (add unsafe 50% (by nlinarith [Real.mul_pos]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [Real.exp_lt_exp]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_right']))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.x_mul_pos]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left]))
      (add unsafe 50% (by nlinarith [Real.b_pos]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r1_pos]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_one_iff]))
      (add unsafe 50% (by nlinarith [div_lt_one]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_right]))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_right']))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.y_mul_pos]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_right]))
      (add unsafe 50% (by nlinarith [Real.add_lt_add_iff_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [lt_div_iff']))
      (add unsafe 50% (by nlinarith [div_lt_iff']))
      (add unsafe 50% (by nlinarith [Behrend.exp_neg_two_mul_le]))
      (add unsafe 50% (by nlinarith [Real.log_lt_iff_lt_exp]))
      (add unsafe 50% (by nlinarith [zero_lt_one]))

  have h10_divide_by_2xyz : 
      1 / (x + y) + 1 / (y + z) + 1 / (z + x) ≥ 9 / (2 * (x + y + z)) := by
    clear * - h8_substitute_nine h9_pos_xyz
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
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
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [one_div_le]))
      (add norm 0 (by grind only [SzemerediRegularity.hundred_div_ε_pow_five_le_m]))
      (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add norm 0 (by grind only [Real.sqrt_one_add_le]))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_one))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [Behrend.two_div_one_sub_two_div_e_le_eight]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))

  have h11_multiply_by_2 : 
      2 / (x + y) + 2 / (y + z) + 2 / (z + x) ≥ 2 * (9 / (2 * (x + y + z))) := by
    clear * - h10_divide_by_2xyz
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
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
      (add safe 100 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by rw [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add norm 0 (by grind only [Real.BohrMollerup.f_add_nat_ge]))
      (add norm 0 (by grind only [mul_add_mul_le_mul_add_mul]))
      (add norm 0 (by grind only [SzemerediRegularity.m_add_one_div_m_le_one_add]))
      (add norm 0 (by grind only [one_add_mul_le_pow]))
      (add norm 0 (by grind only [le_trans]))
      (add norm 0 (by grind only [norm_mul_le_of_le]))
      (add norm 0 (by grind only [SzemerediRegularity.hundred_div_ε_pow_five_le_m]))
      (add norm 0 (by grind only [Real.BohrMollerup.le_logGammaSeq]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_div_right))
      (add safe 1 (by unfold div_le_div_iff))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Real.BohrMollerup.f_add_nat_le]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [Behrend.two_div_one_sub_two_div_e_le_eight]))

  have h12_simplify_rsh : 2 * (9 / (2 * (x + y + z))) = 9 / (x + y + z) := by
    clear * - h9_pos_xyz
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 120
      maxNormIterations := 320
      maxGoals := 512
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
      (add norm 100 (by simp_all))
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
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.Gamma_two]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half_of_pos]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [Real.doublingGamma]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Real.Gamma_mul_Gamma_add_half]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [Real.log_mul]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [one_div]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))

  have h13_final : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    clear * - h11_multiply_by_2 h12_simplify_rsh
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
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
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [le_div_iff]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [div_le_iff']))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_right]))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [Real.pi_le_four]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [le_mul_of_one_le_right']))
      (add norm 0 (by grind only [CircleDeg1Lift.translationNumber_le_of_le_add_int]))
      (add norm 0 (by grind only [div_le_div_right]))
      (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [CircleDeg1Lift.translationNumber_le_of_le_add]))
      (add norm 0 (by grind only [one_le_two]))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_one))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [Real.BohrMollerup.f_add_nat_le]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))

  exact h13_final
