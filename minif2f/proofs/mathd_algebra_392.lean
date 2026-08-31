
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

theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
  -- Step 1: Expand the squares
  have h₂ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (↑n ^ 2 - 4 * ↑n + 4) + ↑n ^ 2 + (↑n ^ 2 + 4 * ↑n + 4) := by
    clear * - h₀ h₁
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
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
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [even_two_mul]))
      (add norm 0 (by grind only [Nat.even_add_one]))
      (add norm 0 (by grind only [Int.even_coe_nat]))
      (add norm 0 (by grind only [Nat.euler_four_squares]))
      (add norm 0 (by grind only [WeierstrassCurve.expDegree_cast]))
      (add norm 0 (by grind only [Int.two_pow_two_pow_add_two_pow_two_pow]))
      (add norm 0 (by grind only [Int.even_add_one]))
      (add norm 0 (by grind only [Int.even_sub_one]))
      (add norm 0 (by grind only [Nat.not_even_two_mul_add_one]))
      (add norm 0 (by grind only [WeierstrassCurve.Ψ_ofNat]))
      (add norm 0 (by grind only [WeierstrassCurve.expCoeff]))
      (add norm 0 (by grind only [WeierstrassCurve.Φ_ofNat]))
      (add norm 0 (by grind only [WeierstrassCurve.expCoeff_cast]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [Nat.even_add]))
      (add norm 0 (by grind only [add_sq]))
      (add norm 0 (by grind only [WeierstrassCurve.b₄]))
      (add norm 0 (by grind only [WeierstrassCurve.Δ]))
      (add norm 0 (by grind only [Int.two_pow_two_pow_sub_pow_two_pow]))
      (add norm 0 (by grind only [WeierstrassCurve.b₂]))
      (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
      (add norm 0 (by grind only [even_iff_two_dvd]))
      (add norm 0 (by grind only [Nat.not_even_one]))
      (add norm 0 (by grind only [Odd.neg_one_pow]))
      (add norm 0 (by grind only [WeierstrassCurve.ψ_odd]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [WeierstrassCurve.coeff_Φ]))
      (add unsafe 50% (by nlinarith [Odd]))
      (add unsafe 50% (by nlinarith [IsSquare]))
      (add unsafe 50% (by nlinarith [Int.even_add]))
      (add unsafe 50% (by nlinarith [Nat.even_or_odd]))
      (add unsafe 50% (by nlinarith [Int.even_sub]))

  -- Step 2: Simplify the expression to 3*n^2 + 8
  have h₃ : (↑n ^ 2 - 4 * ↑n + 4) + ↑n ^ 2 + (↑n ^ 2 + 4 * ↑n + 4) = 3 * ↑n ^ 2 + 8 := by
    clear * - h₂
    classical ring
    zify at h₂ ⊢
    cases' n with n <;> simp <;> ring
    cases n <;> simp [Nat.add_sub_assoc] at * <;> ring_nf at * <;> omega

  -- Step 3: Equate to 12296
  have h₄ : 3 * ↑n ^ 2 + 8 = (12296 : ℤ) := by
    clear * - h₁ h₂ h₃
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      maxGoals := 512
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by zify))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 1 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Pell.xz]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by rw [Zsqrtd.smul_val]))
      (add norm 0 (by rw [Int.cast_mul]))
      (add norm 0 (by rw [Int.cast_pow]))
      (add norm 0 (by grind only [Pell.yz]))
      (add norm 0 (by rw [Int.cast_add]))
      (add norm 0 (by grind only [Pell.x_sub_y_dvd_pow]))
      (add norm 0 (by rw [Int.cast_natCast]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by rw [ZMod.intCast_zmod_eq_zero_iff_dvd]))
      (add norm 0 (by rw [Quaternion.coe_natCast]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by rw [Nat.cast_pow]))
      (add norm 0 (by rw [Int.cast_ofNat]))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by rw [Nat.cast_add]))
      (add norm 0 (by rw [QuaternionAlgebra.coe_natCast]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
      (add norm 0 (by rw [Int.cast_inj]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by rw [Int.ofNat_add]))
      (add norm 0 (by rw [ZNum.of_natCast]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Int.ofNat_mul]))
      (add norm 0 (by grind only [IsMulCentral]))

  -- Step 4: Subtract 8 from both sides
  have h₅ : 3 * ↑n ^ 2 = (12288 : ℤ) := by
    clear * - h₄
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      maxGoals := 512
      enableSimp := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 1 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by rw [Quaternion.star_add_self']))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by rw [Quaternion.self_add_star']))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by grind only [Pell.d]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [sq_add_mul_sq_mul_sq_add_mul_sq]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by rw [Zsqrtd.smul_val]))
      (add norm 0 (by grind only [Int.sq_add_sq_of_two_mul_sq_add_sq]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star']))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [sq_add_sq_mul_sq_add_sq]))
      (add norm 0 (by grind only [Surreal.zsmul_pow_two_powHalf]))

  -- Step 5: Divide by 3
  have h₆ : ↑n ^ 2 = (4096 : ℤ) := by
    clear * - h₅
    aesop (config := {
      maxRuleApplications := 40
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
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [Quaternion.normSq_coe]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by rw [Quaternion.coe_mul]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Quaternion.normSq_intCast]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Real.rpow_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Surreal.zsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [Int.sq_eq_one_of_sq_le_three]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Pell.Solution₁.prop]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [pow_two] at *))

  -- Step 6: Solve for n (n = 64)
  have h₇ : ↑n = (64 : ℤ) := by
    clear * - h₆ h₀
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 520
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 100 (by simp))
      (add safe 100 (by field_simp [*] at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Odd]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Nat.even_pow']))
      (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
      (add norm 0 (by grind only [even_two_mul]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Nat.sq_add_sq_mul]))
      (add norm 0 (by grind only [Int.two_pow_two_pow_add_two_pow_two_pow]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by rw [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [Nat.two_mul_odd_div_two]))
      (add norm 0 (by rw [Nat.cast_pow]))
      (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
      (add unsafe 10% (by grind only [even_iff_two_dvd]))
      (add unsafe 10% (by grind only [Nat.cast_ofNat]))
      (add unsafe 10% (by grind only [jacobiSym.at_two]))
      (add unsafe 50% (by nlinarith [Nat.even_or_odd]))
      (add unsafe 10% (by grind only [Int.cast_ofNat]))
      (add unsafe 10% (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add unsafe 50% (by nlinarith [ZMod.eq_zero_iff_even]))
      (add unsafe 50% (by nlinarith [Nat.even_pow]))
      (add unsafe 10% (by grind only [ZMod.neg_one_pow_div_two_of_one_mod_four]))
      (add unsafe 10% (by grind only [zero_lt_two]))
      (add unsafe 10% (by grind only [irrational_sqrt_of_multiplicity_odd]))
      (add unsafe 50% (by nlinarith [Nat.odd_iff_not_even]))
      (add unsafe 10% (by grind only [FiniteField.odd_card_of_char_ne_two]))
      (add unsafe 50% (by nlinarith [IsSquare]))
      (add unsafe 50% (by nlinarith [Nat.even_mul]))

  -- Step 7: Calculate n - 2
  have h₈ : ↑n - 2 = (62 : ℤ) := by
    clear * - h₇
    aesop (config := {
      maxRuleApplications := 1600
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
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
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [LucasLehmer.Int.coe_nat_two_pow_pred]))
      (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Real.Angle.coe_sub]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux4]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [Complex.sin_two_mul]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [Nat.cast_sub]))
      (add norm 0 (by grind only [div_mul]))
      (add norm 0 (by grind only [Real.Angle.coe_nsmul]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by rw [Quaternion.coe_sub]))
      (add norm 0 (by grind only [eq_div_iff_mul_eq'']))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [QuadraticForm.polar_self]))
      (add safe 1 (by simp_all only [div_eq_iff_eq_mul]))
      (add safe 1 (by simp_all only [div_eq_iff_eq_mul']))
      (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))

  -- Step 8: Calculate n + 2
  have h₉ : ↑n + 2 = (66 : ℤ) := by
    clear * - h₇
    aesop (config := {
      maxRuleApplications := 1600
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
      useDefaultSimpSet := false
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
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by rw [Nat.cast_add]))
      (add norm 0 (by grind only [Finset.mulETransformRight.card]))
      (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
      (add norm 0 (by rw [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Ring.multichoose_two]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by rw [Nat.cast_ofNat]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
      (add norm 0 (by rw [Quaternion.self_add_star']))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))

  -- Step 9: Calculate the product (n-2)*n*(n+2)
  have h₁₀ : (↑n - 2) * ↑n * (↑n + 2) = (62 : ℤ) * (64 : ℤ) * (66 : ℤ) := by
    clear * - h₇ h₈ h₉
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      maxGoals := 512
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [div_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [mul_tsub]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_iff]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_mul_iff]))
      (add norm 0 (by grind only [mul_div_cancel₀]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [tsub_add_cancel_of_le]))
      (add norm 0 (by grind only [half_add_self]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [add_div] at *))

  -- Step 10: Calculate 62 * 64
  have h₁₁ : (62 : ℤ) * (64 : ℤ) = (3968 : ℤ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 256
      enableSimp := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Ring.multichoose_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [zpow_two]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star']))
      (add norm 0 (by grind only [Complex.cosh_two_mul]))
      (add norm 0 (by grind only [Real.cosh_two_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self']))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [Nat.fib_two_mul]))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [mul_comm_of_exponent_two]))
      (add norm 0 (by grind only [Real.sinh_two_mul]))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Complex.two_cosh]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))

  -- Step 11: Calculate 3968 * 66
  have h₁₂ : (3968 : ℤ) * (66 : ℤ) = (261888 : ℤ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 16
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
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [Real.cosh_two_mul]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [zpow_two]))
      (add norm 0 (by grind only [Complex.cosh_two_mul]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Real.sinh_two_mul]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Surreal.zsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [Quaternion.normSq_def']))
      (add norm 0 (by grind only [Real.norm_two]))
      (add norm 0 (by grind only [Quaternion.star_eq_two_re_sub]))
      (add norm 0 (by grind only [Real.rpow_two]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))

  -- Step 12: Combine products
  have h₁₃ : (↑n - 2) * ↑n * (↑n + 2) = (261888 : ℤ) := by
    clear * - h₁₀ h₁₁ h₁₂
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      maxGoals := 512
      useDefaultSimpSet := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [div_mul]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [div_eq_iff_eq_mul]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [eq_div_iff_mul_eq']))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [div_eq_iff]))
      (add norm 0 (by grind only [gosperCatalan]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
      (add norm 0 (by grind only [eq_div_iff_mul_eq]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [QuaternionGroup.xa_mul_xa]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))

  -- Step 13: Divide by 8
  have h₁₄ : (↑n - 2) * ↑n * (↑n + 2) / 8 = (261888 : ℤ) / 8 := by
    clear * - h₁₃
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 120
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
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [div_mul_eq_mul_div]))
      (add norm 0 (by grind only [mul_div_assoc']))
      (add norm 0 (by grind only [tsub_div]))
      (add norm 0 (by grind only [div_add_div_same]))
      (add norm 0 (by grind only [mul_div_left_comm]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 1 (by apply div_mul))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [mul_div_right_comm] at *))
      (add safe 0 (by simp only [div_right_comm] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
      (add safe 0 (by simp only [mul_div_mul_right] at *))
      (add safe 0 (by simp only [half_add_self] at *))
      (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))
      (add safe 0 (by simp only [div_add'] at *))
      (add safe 1 (by apply mul_div_cancel_left))
      (add safe 0 (by simp only [div_left_inj'] at *))
      (add safe 0 (by simp only [Rat.num_div_den] at *))

  -- Step 14: Calculate 261888 / 8
  have h₁₅ : (261888 : ℤ) / 8 = (32736 : ℤ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 120
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      useDefaultSimpSet := false
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
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [goldenConj]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [CircleDeg1Lift.transnumAuxSeq]))
      (add norm 0 (by grind only [gosperCatalan]))
      (add norm 0 (by grind only [add_self_div_two]))
      (add norm 0 (by grind only [mul_div_right_comm]))
      (add norm 0 (by grind only [UpperHalfPlane.sinh_half_dist]))
      (add norm 0 (by grind only [div_pow]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [div_mul] at *))
      (add safe 0 (by simp only [mul_div_mul_right] at *))
      (add safe 0 (by simp only [div_right_comm] at *))
      (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))

  -- Step 15: Final result
  have h₁₆ : (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
    clear * - h₁₄ h₁₅
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 600
      maxNormIterations := 320
      maxGoals := 512
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_div_right_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [div_mul_eq_mul_div]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_div_assoc']))
      (add norm 0 (by grind only [mul_div_left_comm]))
      (add norm 0 (by grind only [gosperCatalan]))
      (add norm 0 (by grind only [div_add_div_same]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [div_mul] at *))
      (add safe 0 (by simp only [mul_div_mul_right] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))
      (add safe 0 (by simp only [div_right_comm] at *))
      (add safe 0 (by simp only [div_add'] at *))
      (add safe 0 (by simp only [div_left_inj'] at *))
      (add safe 0 (by simp only [div_eq_div_iff] at *))
      (add safe 0 (by simp only [Rat.num_div_den] at *))

  exact h₁₆
