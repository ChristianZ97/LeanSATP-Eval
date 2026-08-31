
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

theorem numbertheory_aoddbdiv4asqpbsqmod8eq1 (a : ℤ) (b : ℕ) (h₀ : Odd a) (h₁ : 4 ∣ b) :
    (a ^ 2 + b ^ 2) % 8 = 1 := by
  -- Step 1: Since a is odd, there exists k such that a = 2*k + 1
  have h1 : ∃ k : ℤ, a = 2 * k + 1 := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 600
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 1 (by ring_nf at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Odd]))
      (add norm 0 (by grind only [Stream'.get_odd]))
      (add norm 0 (by grind only [Int.two_pow_two_pow_add_two_pow_two_pow]))
      (add norm 0 (by grind only [Nat.odd_iff_not_even]))
      (add norm 0 (by grind only [Nat.even_add]))
      (add norm 0 (by grind only [Nat.sum_four_squares]))
      (add norm 0 (by grind only [Nat.two_mul_odd_div_two]))
      (add unsafe 10% (by grind only [even_iff_two_dvd]))
      (add unsafe 10% (by grind only [jacobiSym.at_two]))
      (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
      (add unsafe 10% (by grind only [Nat.even_or_odd]))
      (add unsafe 10% (by grind only [irrational_sqrt_of_multiplicity_odd]))
      (add unsafe 10% (by grind only [Nat.even_mul]))
      (add unsafe 50% (by nlinarith [Nat.odd_iff]))
      (add unsafe 10% (by grind only [Int.even_iff]))
      (add unsafe 50% (by nlinarith [Nat.even_iff]))
      (add unsafe 10% (by grind only [IsSquare]))
      (add unsafe 10% (by grind only [Int.emod_two_eq_zero_or_one]))
      (add unsafe 10% (by grind only [FiniteField.odd_card_of_char_ne_two]))
      (add unsafe 50% (by nlinarith [Int.odd_iff_not_even]))
      (add unsafe 50% (by nlinarith [Nat.even_pow]))
      (add unsafe 50% (by nlinarith [Int.emod_eq_zero_of_dvd]))
      (add unsafe 10% (by grind only [Int.even_mul]))
      (add unsafe 50% (by nlinarith [Nat.odd_of_mod_four_eq_three]))
      (add unsafe 50% (by nlinarith [Int.odd_iff]))
      (add unsafe 10% (by grind only [Nat.sq_add_sq_zmodEq]))
      (add unsafe 50% (by nlinarith [Nat.not_even_iff]))
      (add unsafe 10% (by grind only [ZMod.sq_add_sq]))
      (add unsafe 10% (by grind only [ZMod.χ₄_nat_eq_if_mod_four]))
      (add unsafe 50% (by rw [← Int.natCast_inj] at *))
      (add unsafe 50% (by nlinarith [Nat.not_odd_iff]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))

  -- Let k be the witness for a being odd
  obtain ⟨k, hk⟩ := h1
  have h2 : a = 2 * k + 1 := hk

  -- Step 3 & 4: Calculate a^2
  have h3 : a ^ 2 = (2 * k + 1) ^ 2 := by
    clear * - h2
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      maxGoals := 512
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
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by norm_cast at *))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [even_two_mul]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [Surreal.zsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Int.two_pow_two_pow_add_two_pow_two_pow]))
      (add norm 0 (by grind only [add_sq]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [Int.sq_add_sq_of_two_mul_sq_add_sq]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))

  have h4 : a ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by
    clear * - h3
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
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 1 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [sq_add_mul_sq_mul_sq_add_mul_sq]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_y]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [Pell.Solution₁.prop]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Int.sq_of_gcd_eq_one]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [sq_add_sq_mul_sq_add_sq]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [add_sq]))
      (add norm 0 (by grind only [Int.sq_eq_one_of_sq_le_three]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [gaussSum_sq]))

  -- Step 5: Factor out 4k
  have h5 : a ^ 2 = 4 * k * (k + 1) + 1 := by
    clear * - h4
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
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 1 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by grind only [Zsqrtd.smul_val]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [Pell.d]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_pow_mul_iff]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_iff]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Zsqrtd.norm]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imK]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_mul_iff]))
      (add norm 0 (by grind only [Surreal.zsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [Pell.xz]))
      (add norm 0 (by grind only [Metric.glueDist]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))

  -- Step 6: k*(k+1) is always even, so there exists n such that k*(k+1) = 2*n
  have h6 : ∃ n : ℤ, k * (k + 1) = 2 * n := by
    -- The product of two consecutive integers is always even.
    -- If k is even, k=2j, k(k+1)=2j(2j+1)=2(j(2j+1)). Let n=j(2j+1).
    -- If k is odd, k=2j+1, k(k+1)=(2j+1)(2j+2)=(2j+1)*2(j+1)=2((2j+1)(j+1)). Let n=(2j+1)(j+1).
    use k * (k + 1) / 2
    rewrite [mul_comm]
    obtain ⟨l, rfl⟩ | ⟨l, rfl⟩ := Int.even_or_odd k <;> ring_nf <;> omega

  obtain ⟨n, hn⟩ := h6

  -- Step 7 & 8: Substitute back into a^2 expression
  have h7 : a ^ 2 = 4 * (2 * n) + 1 := by
    clear * - h5 hn
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
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Pell.isPell_norm]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Zsqrtd.smul_val]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Zsqrtd.norm]))
      (add norm 0 (by grind only [Surreal.zsmul_pow_two_powHalf]))
      (add norm 0 (by grind only [Pell.d]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Int.sq_add_sq_of_two_mul_sq_add_sq]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
      (add norm 0 (by grind only [Int.sq_eq_one_of_sq_le_three]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))

  have h8 : a ^ 2 = 8 * n + 1 := by
    clear * - h7
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 512
      useDefaultSimpSet := false
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
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Int.sq_add_sq_of_two_mul_sq_add_sq]))
      (add norm 0 (by grind only [Int.sq_eq_one_of_sq_le_three]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [zpow_two]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Int.emod_add_ediv]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Int.sq_of_gcd_eq_one]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [zpow_add]))

  -- Step 9 & 10: Since 4 divides b, there exists m such that b = 4*m
  have h9 : ∃ m : ℕ, b = 4 * m := by
    clear * - h₁
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by push_neg))
      (add safe 0 (by gcongr))
      (add safe 100 (by interval_cases))
      (add safe 100 (by ring_nf))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 100 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by grind only [Nat.sq_mul_squarefree_of_pos]))
      (add unsafe 10% (by grind only [Nat.sq_mul_squarefree]))
      (add unsafe 10% (by grind only [Nat.le_of_dvd]))
      (add unsafe 10% (by grind only [Nat.pos_of_ne_zero]))
      (add unsafe 10% (by grind only [Nat.exists_prime_gt_modEq_one]))
      (add unsafe 10% (by grind only [pos_of_gt]))
      (add unsafe 10% (by grind only [Nat.ord_proj_dvd]))
      (add unsafe 10% (by grind only [Nat.exists_eq_succ_of_ne_zero]))
      (add unsafe 10% (by grind only [Nat.div_pos]))
      (add unsafe 10% (by grind only [Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt]))
      (add unsafe 10% (by grind only [exists_eq_mul_left_of_dvd]))
      (add unsafe 10% (by grind only [Nat.not_dvd_of_pos_of_lt]))
      (add unsafe 10% (by grind only [Nat.pos_of_dvd_of_pos]))
      (add unsafe 10% (by grind only [Nat.eq_zero_or_pos]))
      (add unsafe 10% (by grind only [Nat.sq_mul_squarefree_of_pos']))
      (add unsafe 10% (by grind only [Nat.minSqFacProp_div]))
      (add unsafe 10% (by grind only [dvd_trans]))
      (add unsafe 10% (by grind only [Nat.div_dvd_of_dvd]))
      (add unsafe 10% (by grind only [Nat.strong_induction_on]))
      (add unsafe 10% (by grind only [Nat.ord_proj_pos]))
      (add unsafe 10% (by grind only [Nat.exists_mul_emod_eq_one_of_coprime]))
      (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
      (add unsafe 10% (by grind only [Nat.dvd_of_mem_primeFactors]))
      (add unsafe 10% (by grind only [Nat.sq_add_sq_zmodEq]))
      (add unsafe 10% (by grind only [Nat.div_lt_self]))
      (add unsafe 10% (by grind only [Pell.eq_pell]))
      (add unsafe 10% (by grind only [Nat.dvd_factorial]))
      (add unsafe 10% (by grind only [Nat.gcd_eq_right]))
      (add unsafe 10% (by grind only [dvd_refl]))
      (add unsafe 10% (by grind only [Nat.exists_infinite_pseudoprimes]))
      (add unsafe 10% (by grind only [Nat.Prime.one_lt]))
      (add unsafe 10% (by grind only [Nat.ord_proj_le]))

  obtain ⟨m, hm⟩ := h9

  have h10 : b = 4 * m := hm

  -- Step 10 & 11: Calculate b^2
  have h11 : b ^ 2 = (4 * m) ^ 2 := by
    clear * - h10
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Nat.sq_sub_sq]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [pow_mul']))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [Nat.even_pow']))
      (add norm 0 (by grind only [Nat.sq_add_sq_mul]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [qrSign.neg_one_pow]))
      (add norm 0 (by grind only [nat_sub_dvd_pow_sub_pow]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [Nat.bp_helper]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))

  have h12 : b ^ 2 = 16 * m ^ 2 := by
    clear * - h11
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
      (add norm 1 (by ext))
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
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [ZMod.χ₄_eq_neg_one_pow]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [Nat.sq_sub_sq]))
      (add norm 0 (by grind only [legendreSym.sq_one']))
      (add norm 0 (by grind only [Int.isUnit_sq]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq]))
      (add norm 0 (by grind only [Even.neg_one_pow]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [qrSign.neg_one_pow]))
      (add norm 0 (by grind only [nat_sub_dvd_pow_sub_pow]))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
      (add norm 0 (by grind only [pow_ne_zero]))
      (add norm 0 (by grind only [pow_mul']))
      (add norm 0 (by grind only [Nat.even_pow']))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [pow_add]))

  have h13 : b ^ 2 = 8 * (2 * m ^ 2) := by
    clear * - h12
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
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
      (add norm 100 (by split))
      (add norm 0 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [pow_mul]))
      (add norm 0 (by grind only [quadraticChar_sq_one]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [neg_one_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [legendreSym.sq_one]))
      (add norm 0 (by grind only [Nat.sq_add_sq_mul]))
      (add norm 0 (by grind only [qrSign.sq_eq_one]))
      (add norm 0 (by grind only [pow_pos]))
      (add norm 0 (by grind only [Nat.sq_sub_sq]))
      (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [Nat.even_pow']))
      (add norm 0 (by grind only [ZMod.neg_one_pow_div_two_of_three_mod_four]))
      (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
      (add norm 0 (by grind only [MulChar.IsQuadratic.sq_eq_one]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [euler_four_squares]))
      (add unsafe 90% (by simp only [pow_two] at *))

  -- Step 12 & 13: Sum a^2 and b^2
  have h14 : a ^ 2 + b ^ 2 = (8 * n + 1) + 8 * (2 * m ^ 2) := by
    clear * - h8 h13
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
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
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 1 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by rw [Nat.cast_ofNat]))
      (add norm 0 (by grind only [Nat.cast_add]))
      (add norm 0 (by rw [Nat.cast_pow]))
      (add norm 0 (by rw [Nat.cast_npow]))
      (add norm 0 (by rw [Quaternion.coe_natCast]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [jacobiSym.mul_left]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [qrSign.symm]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Int.ofNat_mul]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [Nat.cast_succ]))
      (add norm 0 (by rw [QuaternionAlgebra.coe_natCast]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Pell.x_sub_y_dvd_pow]))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [qrSign.neg_one_pow]))
      (add norm 0 (by grind only [jacobiSym.quadratic_reciprocity]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by rw [Int.ofNat_add]))
      (add norm 0 (by grind only [qrSign]))
      (add norm 0 (by grind only [pow_succ]))
      (add norm 0 (by rw [Int.cast_pow]))
      (add norm 0 (by grind only [Pell.xz]))

  have h15 : a ^ 2 + b ^ 2 = 8 * (n + 2 * m ^ 2) + 1 := by
    clear * - h14
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
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by zify))
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
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [pow_add]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [Int.two_pow_two_pow_add_two_pow_two_pow]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [even_two_mul]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by rw [Nat.cast_ofNat]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [pow_succ]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [Pell.xz]))
      (add norm 0 (by grind only [add_sq]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Odd]))

  -- Step 14: Conclude modulo 8
  have h16 : (a ^ 2 + b ^ 2) % 8 = 1 := by
    clear * - h15
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      maxGoals := 16
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 0 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.mod_two_add_succ_mod_two]))
      (add norm 0 (by grind only [mul_assoc]))
      (add unsafe 50% (by nlinarith [Nat.mod_mod]))
      (add unsafe 50% (by nlinarith [neg_one_pow_eq_pow_mod_two]))
      (add unsafe 50% (by nlinarith [Nat.mul_mod]))
      (add unsafe 50% (by nlinarith [Nat.odd_iff]))
      (add unsafe 50% (by nlinarith [Nat.pow_mod]))
      (add unsafe 50% (by nlinarith [Nat.mod_mod_of_dvd]))
      (add unsafe 50% (by nlinarith [Nat.mul_mod_left]))
      (add unsafe 50% (by nlinarith [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
      (add unsafe 50% (by nlinarith [Nat.ModEq]))
      (add unsafe 50% (by nlinarith [Nat.even_iff]))
      (add unsafe 50% (by nlinarith [Nat.gcd.induction]))
      (add unsafe 50% (by nlinarith [Int.natCast_mod]))
      (add unsafe 50% (by nlinarith [Int.mul_emod]))
      (add unsafe 50% (by nlinarith [Nat.mod_two_ne_zero]))
      (add unsafe 50% (by nlinarith [Nat.mod_mul_left_mod]))
      (add unsafe 50% (by nlinarith [jacobiSym.quadratic_reciprocity_one_mod_four]))
      (add unsafe 50% (by nlinarith [Nat.mul_mod_mod]))
      (add unsafe 50% (by nlinarith [Nat.mod_eq_zero_of_dvd]))
      (add unsafe 50% (by nlinarith [Nat.mod_two_ne_one]))
      (add unsafe 50% (by nlinarith [Int.emod_emod_of_dvd]))
      (add unsafe 50% (by nlinarith [Nat.mul_mod_right]))
      (add unsafe 50% (by nlinarith [Int.ModEq]))
      (add unsafe 50% (by nlinarith [Nat.mod_mul_mod]))
      (add unsafe 50% (by nlinarith [ZMod.natCast_mod]))
      (add unsafe 50% (by nlinarith [Int.emod_eq_zero_of_dvd]))
      (add unsafe 50% (by nlinarith [Int.ofNat_emod]))
      (add unsafe 50% (by nlinarith [Num.mod_to_nat]))
      (add unsafe 50% (by nlinarith [Int.emod_two_ne_one]))
      (add unsafe 50% (by nlinarith [ZMod.natCast_eq_natCast_iff']))
      (add unsafe 50% (by nlinarith [Int.emod_emod]))

  exact h16
