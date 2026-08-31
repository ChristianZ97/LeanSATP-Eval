
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

theorem mathd_numbertheory_222 (b : ℕ) (h₀ : Nat.lcm 120 b = 3720) (h₁ : Nat.gcd 120 b = 8) :
    b = 248 := by
  -- Step 1: Use the property that lcm(a, b) * gcd(a, b) = a * b
  have h₂ : Nat.lcm 120 b * Nat.gcd 120 b = 120 * b := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 16
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.gcd_mul_lcm]))
      (add norm 0 (by grind only [PNat.gcd_a_eq]))
      (add norm 0 (by grind only [Nat.gcd]))
      (add norm 0 (by grind only [Nat.gcd_eq_gcd_ab]))
      (add norm 0 (by grind only [PNat.gcd]))
      (add norm 0 (by grind only [Int.gcd_eq_natAbs]))
      (add norm 0 (by grind only [Int.gcd_eq_gcd_ab]))
      (add norm 0 (by grind only [PNat.gcd_rel_left]))
      (add norm 0 (by grind only [Int.gcd_comm]))
      (add norm 0 (by grind only [PNat.gcd_b_eq]))
      (add norm 0 (by grind only [ZMod.mul_inv_eq_gcd]))
      (add norm 0 (by grind only [Nat.totient_gcd_mul_totient_mul]))
      (add norm 0 (by grind only [Int.coe_gcd]))
      (add norm 0 (by grind only [Nat.gcd_mul_left_left]))
      (add norm 0 (by grind only [Nat.fib_gcd]))
      (add norm 0 (by rw [Int.gcd_natCast_natCast]))
      (add norm 0 (by grind only [Nat.gcd_dvd_left]))
      (add norm 0 (by grind only [Nat.coprime_iff_gcd_eq_one]))
      (add norm 0 (by grind only [Int.gcd]))
      (add norm 0 (by grind only [Nat.gcd_mul_left_right]))
      (add norm 0 (by grind only [Nat.gcd_fib_add_mul_self]))
      (add norm 0 (by grind only [PNat.gcd_mul_lcm]))
      (add norm 0 (by grind only [Nat.gcd_mul_left]))
      (add norm 0 (by grind only [Nat.Coprime.gcd_eq_one]))
      (add norm 0 (by grind only [Nat.coprime_of_squarefree_mul]))
      (add norm 0 (by grind only [PNat.gcd_coe]))
      (add norm 0 (by grind only [Nat.mul_left_eq_self_iff]))
      (add norm 0 (by rw [Int.isCoprime_iff_gcd_eq_one]))
      (add norm 0 (by grind only [Nat.periodic_gcd]))
      (add norm 0 (by grind only [Int.gcd_eq_one_iff_coprime]))
      (add norm 0 (by grind only [PNat.gcd_comm]))
      (add norm 0 (by grind only [gcd_eq_nat_gcd]))

  -- Step 2: Substitute h₀ and h₁ into h₂
  have h₃ : 3720 * Nat.gcd 120 b = 120 * b := by
    clear * - h₀ h₂
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
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
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by split))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [PNat.gcd_a_eq]))
      (add norm 0 (by rw [Nat.gcd_eq_gcd_ab]))
      (add norm 0 (by grind only [Int.gcd_eq_gcd_ab]))
      (add norm 0 (by grind only [PNat.gcd_b_eq]))
      (add norm 0 (by grind only [Nat.totient_gcd_mul_totient_mul]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by rw [Zsqrtd.smul_val]))
      (add norm 0 (by grind only [Nat.gcd_mul_lcm]))
      (add norm 0 (by grind only [PNat.gcd_rel_left]))
      (add norm 0 (by grind only [Nat.gcd_dvd_left]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_iff]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by grind only [Nat.gcd_dvd_right]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_mul_iff]))
      (add norm 0 (by grind only [Int.gcd_comm]))
      (add norm 0 (by grind only [PNat.gcd_mul_lcm]))
      (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero_z]))
      (add norm 0 (by grind only [Int.coe_gcd]))
      (add norm 0 (by grind only [PNat.gcd]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Pell.d]))
      (add norm 0 (by grind only [Int.gcd]))
      (add norm 0 (by grind only [PNat.gcd_det_eq]))
      (add norm 0 (by grind only [ZMod.mul_inv_eq_gcd]))
      (add norm 0 (by grind only [Zsqrtd]))
      (add norm 0 (by grind only [PNat.gcd_rel_left']))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))

  -- Step 3: Substitute h₁ into h₃ to get 3720 * 8 = 120 * b
  have h₄ : 3720 * 8 = 120 * b := by
    clear * - h₁ h₃
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 512
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
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 100 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by split))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Nat.gcd_eq_gcd_ab]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Int.gcd_eq_gcd_ab]))
      (add norm 0 (by grind only [Nat.gcd_dvd_left]))
      (add norm 0 (by grind only [Nat.gcd_dvd_right]))
      (add norm 0 (by grind only [Nat.totient_gcd_mul_totient_mul]))
      (add norm 0 (by grind only [PNat.gcd_a_eq]))
      (add norm 0 (by grind only [Int.gcd]))
      (add norm 0 (by rw [Int.gcd_natCast_natCast]))
      (add norm 0 (by grind only [Int.mul_ediv_cancel']))
      (add norm 0 (by grind only [Int.coe_gcd]))
      (add norm 0 (by grind only [Int.gcd_comm]))
      (add norm 0 (by grind only [Nat.mul_div_cancel_left]))
      (add norm 0 (by grind only [Int.ediv_mul_cancel]))
      (add norm 0 (by grind only [Nat.div_mul_cancel]))
      (add norm 0 (by grind only [Nat.coprime_div_gcd_div_gcd]))
      (add norm 0 (by grind only [Int.ofNat_mul]))
      (add norm 0 (by grind only [Nat.mul_div_left]))
      (add norm 0 (by grind only [Nat.coprime_div_gcd_of_squarefree]))
      (add norm 0 (by grind only [Int.mul_ediv_cancel_left]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by grind only [Int.natCast_mul]))
      (add norm 0 (by grind only [Pell.d]))
      (add norm 0 (by grind only [Nat.mul_div_cancel']))
      (add norm 0 (by grind only [PNat.gcd_b_eq]))
      (add norm 0 (by grind only [Nat.mul_div_right]))
      (add norm 0 (by grind only [PNat.gcd_rel_left]))
      (add norm 0 (by grind only [Int.eq_mul_of_ediv_eq_left]))
      (add norm 0 (by grind only [Nat.mul_div_cancel]))

  -- Step 4: Calculate 3720 * 8 = 29760
  have h₅ : 29760 = 120 * b := by
    clear * - h₄
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 16
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
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
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Nat.div_add_mod]))
      (add norm 0 (by grind only [SimpleGraph.aux]))
      (add norm 0 (by grind only [Nat.two_mul_odd_div_two]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Pell.d]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Nat.two_mul_div_two_add_one_of_odd]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [Nat.div_add_mod']))
      (add norm 0 (by grind only [Nat.fib_two_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [Nat.succ_mul_centralBinom_succ]))
      (add norm 0 (by rw [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Sym2.two_mul_card_image_offDiag]))
      (add norm 0 (by grind only [Nat.add_mul_div_left]))
      (add norm 0 (by grind only [gosperCatalan]))
      (add norm 0 (by grind only [Nat.mul_div_left]))
      (add norm 0 (by grind only [Pell.isPell_norm]))

  -- Step 5: Solve for b: b = 29760 / 120
  -- We need to be careful with division in natural numbers. 
  -- Instead of dividing directly, we can state that 120 * 248 = 29760
  have h₆ : 120 * 248 = 29760 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 256
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [sq_ne_two_fin_zmod_four]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by rw [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by rw [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [Nat.squarefree_two]))
      (add norm 0 (by grind only [Nat.superFactorial_two_mul]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [DihedralGroup.div_two_lt]))
      (add norm 0 (by grind only [Nat.two_mul_odd_div_two]))
      (add norm 0 (by grind only [Surreal.zsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Nat.mul_two]))
      (add unsafe 10% (by grind only [SimpleGraph.aux]))
      (add unsafe 10% (by grind only [zero_lt_two]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))

  -- Step 6: From h₅ and h₆, we have 120 * b = 120 * 248
  have h₇ : 120 * b = 120 * 248 := by
    clear * - h₅ h₆
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 256
      enableSimp := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
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
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Eq.symm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [Eq.trans]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by grind only [gosperCatalan]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Nat.succ_mul_centralBinom_succ]))
      (add norm 0 (by rw [Zsqrtd.smul_val]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [mul_left_cancel₀]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [QuaternionAlgebra.coe_commutes]))
      (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero_z]))
      (add norm 0 (by grind only [Nat.centralBinom]))
      (add norm 0 (by grind only [FractionalIdeal.dual_mul_self]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by rw [Nat.gcd_eq_gcd_ab]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [Pell.d]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by grind only [Sym2.two_mul_card_image_offDiag]))
      (add norm 0 (by grind only [Pell.dz_val]))

  -- Step 7: Cancel 120 from both sides to get b = 248
  have h₈ : b = 248 := by
    clear * - h₇
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 256
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
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [Nat.mul_ne_zero]))
      (add norm 0 (by grind only [mul_comm_of_exponent_two]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Nat.two_mul_odd_div_two]))
      (add norm 0 (by grind only [Nat.mul_right_inj]))
      (add norm 0 (by grind only [Nat.sq_add_sq_mul]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [nat_mul_inj']))
      (add norm 0 (by grind only [Nat.mul_div_left]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add unsafe 10% (by grind only [SimpleGraph.aux]))
      (add unsafe 10% (by grind only [mul_left_cancel₀]))
      (add unsafe 10% (by grind only [Nat.add_div]))
      (add unsafe 10% (by grind only [zero_lt_two]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add unsafe 10% (by grind only [sq_ne_two_fin_zmod_four]))
      (add unsafe 10% (by grind only [DihedralGroup.div_two_lt]))
      (add unsafe 10% (by grind only [mul_right_inj']))
      (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
      (add unsafe 10% (by grind only [Nat.mod_lt]))
      (add unsafe 10% (by grind only [Nat.mul_pos]))
      (add unsafe 10% (by grind only [Nat.div_lt_self]))
      (add unsafe 10% (by grind only [Nat.mul_lt_mul_left]))
      (add unsafe 10% (by grind only [Nat.div_pos]))
      (add unsafe 10% (by grind only [Nat.le_mul_of_pos_left]))
      (add unsafe 10% (by grind only [Nat.pos_of_ne_zero]))
      (add unsafe 10% (by grind only [LucasLehmer.two_lt_q]))
      (add unsafe 10% (by grind only [Pell.eq_pow_of_pell_lem]))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
      (add unsafe 10% (by grind only [Nat.div_lt_iff_lt_mul']))
      (add unsafe 10% (by grind only [gold_lt_two]))

  exact h₈
