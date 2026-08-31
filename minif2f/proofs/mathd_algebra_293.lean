
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

theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have h1 : (60 : ℝ) * (12 : ℝ) * (63 : ℝ) = 45360 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 60
      maxGoals := 256
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by rw [Quaternion.coe_mul_eq_smul]))
      (add norm 0 (by rw [Quaternion.coe_mul]))
      (add norm 0 (by grind only [Quaternion.mul_coe_eq_smul]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Quaternion.self_mul_star]))
      (add norm 0 (by grind only [Quaternion.star_mul_self]))
      (add norm 0 (by grind only [Real.cosh_sq']))
      (add norm 0 (by grind only [Quaternion.normSq_def']))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.cosh_two_mul]))
      (add norm 0 (by grind only [Real.sinh_two_mul]))
      (add norm 0 (by grind only [Quaternion.star_mul_eq_coe]))
      (add norm 0 (by grind only [Complex.sq_abs]))
      (add norm 0 (by grind only [Complex.two_cosh]))
      (add norm 0 (by grind only [Quaternion.mul_star_eq_coe]))
      (add norm 0 (by grind only [sq_add_sq_mul_sq_add_sq]))
      (add norm 0 (by grind only [Real.cosh_eq_tsum]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [UpperHalfPlane.cosh_dist]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Quaternion.normSq_add]))
      (add norm 0 (by grind only [Real.cosh_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))

  have h2 : (45360 : ℝ) = (1296 : ℝ) * (35 : ℝ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 16
      enableSimp := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 1 (by ring_nf at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_bit0]))
      (add norm 0 (by grind only [mul_bit1]))
      (add norm 0 (by grind only [Int.bit_val]))
      (add norm 0 (by rw [ArithmeticFunction.moebius_mul_coe_zeta]))
      (add norm 0 (by grind only [Matrix.zpow_bit0]))
      (add norm 0 (by rw [Matrix.SpecialLinearGroup.coe_mul]))
      (add norm 0 (by grind only [bit0_eq_two_mul]))
      (add norm 0 (by grind only [Nat.bit1_div_two]))
      (add norm 0 (by rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]))
      (add norm 0 (by grind only [Nat.bit0_div_two]))
      (add norm 0 (by grind only [Rat.cast_bit1]))
      (add norm 0 (by grind only [Int.bit]))
      (add norm 0 (by grind only [ZNum.cast_bit1]))
      (add norm 0 (by grind only [bit1_mul]))
      (add norm 0 (by grind only [ZNum.cast_bit0]))
      (add norm 0 (by grind only [Nat.bit_val]))
      (add norm 0 (by grind only [bit1]))
      (add norm 0 (by grind only [PosNum.divMod]))
      (add norm 0 (by rw [ArithmeticFunction.intCoe_one]))
      (add norm 0 (by grind only [Rat.cast_bit0]))
      (add norm 0 (by grind only [CharTwo.bit1_apply_eq_one]))
      (add norm 0 (by grind only [Num.cast_bit0]))
      (add norm 0 (by grind only [Nat.bit_mod_two]))
      (add norm 0 (by grind only [bit0_mul]))
      (add norm 0 (by grind only [Nat.bit0_val]))
      (add norm 0 (by grind only [Nat.cast_bit1]))
      (add norm 0 (by grind only [ZNum.bit1]))
      (add norm 0 (by grind only [Nat.cast_bit0]))
      (add norm 0 (by rw [ArithmeticFunction.coe_coe]))
      (add norm 0 (by rw [ArithmeticFunction.mul_apply_one]))
      (add norm 0 (by grind only [Tropical.bit0]))
      (add norm 0 (by grind only [bit0]))

  have h3 : Real.sqrt (60 * ↑x) * Real.sqrt (12 * ↑x) * Real.sqrt (63 * ↑x) = Real.sqrt (45360 * ↑x ^ 3) := by
    clear * -
    have := x.2
    repeat rw [← Real.sqrt_mul (by positivity)]; ring_nf

  have h4 : Real.sqrt (45360 * ↑x ^ 3) = Real.sqrt ((1296 : ℝ) * (35 : ℝ) * ↑x ^ 2 * ↑x) := by
    clear * - h1 h2
    congr 1 <;> norm_cast <;> ring

  have h5 : Real.sqrt ((1296 : ℝ) * (35 : ℝ) * ↑x ^ 2 * ↑x) = Real.sqrt (1296) * Real.sqrt (↑x ^ 2) * Real.sqrt (35 * ↑x) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [Real.coe_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [NNReal.sq_sqrt]))
      (add norm 0 (by grind only [NNReal.rpow_two]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [NNReal.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [NNReal.sqrt_eq_rpow]))
      (add norm 0 (by grind only [NNReal.coe_pow]))
      (add norm 0 (by grind only [NNReal.sqrt_sq]))
      (add norm 0 (by grind only [NNReal.coe_mul]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [WithLp.prod_norm_sq_eq_of_L2]))
      (add norm 0 (by grind only [PiLp.norm_eq_of_L2]))
      (add norm 0 (by grind only [WithLp.prod_nnnorm_eq_of_L2]))
      (add norm 0 (by grind only [IsSelfAdjoint.sq_spectrumRestricts]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Matrix.frobenius_nnnorm_col]))
      (add norm 0 (by grind only [ENNReal.coe_pow]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodySumFactor]))
      (add norm 0 (by grind only [NNReal.coe_rpow]))
      (add norm 0 (by grind only [PiLp.norm_sq_eq_of_L2]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodyLTFactor]))
      (add norm 0 (by grind only [NNReal.sqrt]))
      (add norm 0 (by grind only [Quaternion.nnnorm_coe]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [NNReal.coe_ofNat]))
      (add norm 0 (by grind only [Quaternion.nnnorm_star]))

  have h6 : Real.sqrt (1296 : ℝ) = 36 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [Real.sqrt_one]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [Real.cos_half]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [NNReal.rpow_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [irrational_sqrt_two]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [integral_gaussian]))
      (add norm 0 (by grind only [Real.sin_half_eq_sqrt]))
      (add norm 0 (by grind only [Complex.abs_le_sqrt_two_mul_max]))
      (add norm 0 (by grind only [PiLp.norm_eq_of_L2]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [EuclideanSpace.dist_eq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Real.abs_sin_half]))
      (add norm 0 (by grind only [Real.sqrt_inv]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 90% (by simp only [pow_two] at *))

  have h7 : Real.sqrt (↑x ^ 2) = ↑x := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [Real.coe_sqrt]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodySumFactor]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [PiLp.norm_eq_of_L2]))
      (add norm 0 (by grind only [NNReal.sq_sqrt]))
      (add norm 0 (by grind only [Complex.volume_ball]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [NNReal.coe_pow]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [NNReal.coe_ofNat]))
      (add norm 0 (by grind only [NNReal.sqrt_eq_rpow]))
      (add norm 0 (by grind only [ENNReal.coe_pow]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodyLTFactor]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [WithLp.prod_norm_sq_eq_of_L2]))
      (add norm 0 (by grind only [NNReal.coe_two]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [NNReal.sqrt_sq]))
      (add norm 0 (by grind only [ENNReal.ofReal_pow]))
      (add norm 0 (by grind only [NNReal.coe_real_pi]))
      (add norm 0 (by grind only [ENNReal.coe_ofNat]))
      (add norm 0 (by grind only [Quaternion.norm_piLp_equiv_symm_equivTuple]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add unsafe 90% (by simp only [NNReal.rpow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_sub_sq]))

  have h8 : Real.sqrt ((1296 : ℝ) * (35 : ℝ) * ↑x ^ 2 * ↑x) = 36 * ↑x * Real.sqrt (35 * ↑x) := by
    clear * - h5 h6 h7
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 60
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [Real.coe_sqrt]))
      (add norm 0 (by grind only [NNReal.coe_mul]))
      (add norm 0 (by grind only [NNReal.sqrt_mul]))
      (add norm 0 (by grind only [NNReal.coe_rpow]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [NNReal.sqrt_eq_rpow]))
      (add norm 0 (by grind only [NNReal.coe_pow]))
      (add norm 0 (by grind only [NNReal.sq_sqrt]))
      (add norm 0 (by grind only [Quaternion.nnnorm_coe]))
      (add norm 0 (by grind only [Real.toNNReal_mul]))
      (add norm 0 (by grind only [NNReal.sqrt_sq]))
      (add norm 0 (by grind only [NNReal.sqrt]))
      (add norm 0 (by grind only [WithLp.prod_nnnorm_eq_of_L2]))
      (add norm 0 (by grind only [NNReal.coe_inv]))
      (add norm 0 (by grind only [Quaternion.nnnorm_star]))
      (add norm 0 (by grind only [ENNReal.coe_pow]))
      (add norm 0 (by grind only [NNReal.sqrt_inv]))
      (add norm 0 (by grind only [NNReal.rpow_two]))
      (add norm 0 (by grind only [NumberField.mixedEmbedding.convexBodyLTFactor]))
      (add norm 0 (by grind only [NNReal.mul_rpow]))
      (add norm 0 (by grind only [NNReal.val_eq_coe]))
      (add norm 0 (by grind only [NNReal.coe_mk]))
      (add norm 0 (by grind only [NNReal.norm_eq]))
      (add norm 0 (by grind only [ENNReal.coe_inj]))
      (add norm 0 (by grind only [norm_toNNReal']))
      (add norm 0 (by grind only [QuasispectrumRestricts.nnreal_iff]))
      (add norm 0 (by grind only [Real.toNNReal_coe]))
      (add norm 0 (by grind only [Matrix.frobenius_nnnorm_col]))
      (add norm 0 (by grind only [nnnorm_mul]))
      (add norm 0 (by grind only [Real.coe_toNNReal]))

  have h9 : Real.sqrt (60 * ↑x) * Real.sqrt (12 * ↑x) * Real.sqrt (63 * ↑x) = 36 * ↑x * Real.sqrt (35 * ↑x) := by
    clear * - h3 h4 h8
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 60
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.coe_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [NNReal.coe_mul]))
      (add norm 0 (by grind only [NNReal.sqrt_mul]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.toNNReal_mul]))
      (add norm 0 (by grind only [NNReal.coe_rpow]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [NNReal.coe_pow]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [NNReal.sq_sqrt]))
      (add norm 0 (by grind only [Quaternion.nnnorm_coe]))
      (add norm 0 (by grind only [Quaternion.nnnorm_star]))
      (add norm 0 (by grind only [NNReal.sqrt_eq_rpow]))
      (add norm 0 (by grind only [NNReal.sqrt]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [IsSelfAdjoint.sq_spectrumRestricts]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [NNReal.sqrt_le_iff_le_sq]))
      (add norm 0 (by grind only [NNReal.sqrt_sq]))
      (add norm 0 (by grind only [NNReal.rpow_two]))
      (add norm 0 (by grind only [QuasispectrumRestricts.nnreal_iff]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [WithLp.prod_nnnorm_eq_of_L2]))
      (add norm 0 (by grind only [NNReal.mul_rpow]))
      (add norm 0 (by grind only [nnnorm_mul]))
      (add norm 0 (by grind only [NNReal.coe_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_mul_self_eq_abs]))

  exact h9
