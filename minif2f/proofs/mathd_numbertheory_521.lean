
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

theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  -- Step 1: From h2, we have m - n = 2
  have h_step1 : m - n = 2 := by
    clear * - h₂
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
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
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [eq_comm]))
      (add norm 0 (by grind only [div_eq_iff_eq_mul']))
      (add norm 0 (by grind only [tsub_eq_iff_eq_add_of_le]))
      (add norm 0 (by grind only [eq_tsub_iff_add_eq_of_le]))
      (add norm 0 (by grind only [Basis.ext_elem_iff]))
      (add norm 0 (by grind only [Polynomial.mirror_eq_iff]))
      (add norm 0 (by grind only [Nat.sub_eq_zero_iff_le]))
      (add norm 0 (by grind only [div_eq_one]))
      (add norm 0 (by grind only [eq_tsub_of_add_eq]))
      (add norm 0 (by grind only [AffineSubspace.right_mem_perpBisector]))
      (add norm 0 (by grind only [div_eq_iff_eq_mul]))
      (add norm 0 (by grind only [Real.arccos_eq_pi]))
      (add norm 0 (by grind only [Tropical.untrop_inj_iff]))
      (add norm 0 (by grind only [AffineSubspace.left_mem_perpBisector]))
      (add norm 0 (by grind only [toIocMod_eq_toIocMod]))
      (add norm 0 (by grind only [Polynomial.mirror_inj]))
      (add norm 0 (by grind only [inv_smul_eq_iff]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [smul_eq_iff_eq_inv_smul]))
      (add norm 0 (by grind only [Zspan.fract_eq_self]))
      (add norm 0 (by grind only [eq_div_iff_mul_eq']))
      (add norm 0 (by grind only [Real.neg_pi_div_two_eq_arcsin]))
      (add norm 0 (by grind only [star_eq_iff_star_eq]))
      (add norm 0 (by grind only [Nat.add_sub_cancel]))
      (add norm 0 (by grind only [Nat.cast_tsub]))
      (add norm 0 (by grind only [Nat.add_sub_cancel_right]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Nat.sub_sub_sub_cancel_right]))
      (add norm 0 (by grind only [Quaternion.coe_inj]))
      (add norm 0 (by grind only [EmbeddingLike.apply_eq_iff_eq]))
      (add norm 0 (by grind only [Nat.sub_right_comm]))
      (add norm 0 (by grind only [star_inj]))

  -- Step 2: We want to express m in terms of n. 
  -- Since m and n are natural numbers and m - n = 2, this implies m >= n and m = n + 2.
  -- However, subtraction in Nat is truncated. We need to be careful.
  -- Given m * n = 288, both m and n are positive.
  -- If m < n, then m - n = 0 in Nat, which contradicts h_step1 (0 != 2). So m > n.
  have h_m_ge_n : n ≤ m := by
    clear * - h_step1
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
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
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add norm 0 (by grind only [Nat.sub_add_comm]))
      (add norm 0 (by grind only [Nat.add_sub_cancel']))
      (add norm 0 (by grind only [Nat.sub_add_cancel]))
      (add norm 0 (by grind only [Nat.add_sub_assoc]))
      (add norm 0 (by grind only [Nat.sub_sub_self]))
      (add norm 0 (by grind only [Nat.add_sub_cancel]))
      (add norm 0 (by grind only [Nat.add_sub_of_le]))
      (add norm 0 (by grind only [Nat.le_sub_of_add_le']))
      (add norm 0 (by grind only [Nat.sub_sub]))
      (add norm 0 (by grind only [Nat.add_sub_cancel_left]))
      (add norm 0 (by grind only [tsub_tsub_cancel_of_le]))
      (add norm 0 (by grind only [Nat.sub_right_comm]))
      (add norm 0 (by grind only [Nat.sub_add_sub_cancel]))
      (add norm 0 (by grind only [Nat.sub_le_sub_right]))
      (add norm 0 (by grind only [tsub_tsub]))
      (add norm 0 (by grind only [Nat.add_sub_cancel_right]))
      (add norm 0 (by grind only [tsub_add_cancel_of_le]))
      (add norm 0 (by grind only [Nat.sub_eq_zero_of_le]))
      (add norm 0 (by grind only [Nat.cast_tsub]))
      (add norm 0 (by grind only [add_tsub_cancel_left]))
      (add norm 0 (by grind only [eq_tsub_of_add_eq]))
      (add norm 0 (by grind only [add_tsub_cancel_right]))
      (add norm 0 (by grind only [Nat.sub_sub_sub_cancel_right]))
      (add norm 0 (by grind only [Nat.add_sub_add_right]))
      (add norm 0 (by grind only [tsub_tsub_assoc]))
      (add norm 0 (by grind only [Nat.even_sub]))
      (add norm 0 (by grind only [add_tsub_cancel_of_le]))
      (add norm 0 (by grind only [tsub_add_eq_add_tsub]))
      (add norm 0 (by grind only [Nat.sub_add_eq]))
      (add norm 0 (by grind only [Nat.sub_self]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add unsafe 10% (by grind only [Nat.sub_le]))

  -- Step 3: From m - n = 2 and n <= m, we can deduce m = n + 2.
  -- In Lean's Nat, if n <= m, then m - n + n = m. 
  -- Here m - n = 2, so 2 + n = m.
  have h_step3 : m = n + 2 := by
    clear * - h_step1 h_m_ge_n
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
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
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.add_sub_cancel]))
      (add norm 0 (by grind only [Nat.add_sub_assoc]))
      (add norm 0 (by grind only [Nat.add_sub_cancel']))
      (add norm 0 (by grind only [Nat.sub_add_comm]))
      (add norm 0 (by grind only [Nat.sub_add_cancel]))
      (add norm 0 (by grind only [Nat.add_sub_cancel_left]))
      (add norm 0 (by grind only [Nat.add_sub_of_le]))
      (add norm 0 (by grind only [add_tsub_cancel_left]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [add_tsub_cancel_right]))
      (add norm 0 (by grind only [tsub_add_cancel_of_le]))
      (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
      (add norm 0 (by grind only [Nat.add_sub_cancel_right]))
      (add norm 0 (by grind only [add_tsub_cancel_of_le]))
      (add norm 0 (by grind only [Finset.mulETransformRight.card]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [Nat.sub_sub]))
      (add norm 0 (by grind only [tsub_add_eq_add_tsub]))
      (add norm 0 (by grind only [Nat.add_sub_add_right]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Nat.sub_add_sub_cancel]))
      (add norm 0 (by grind only [eq_tsub_of_add_eq]))
      (add norm 0 (by grind only [Nat.succ_add_sub_one]))
      (add norm 0 (by grind only [Nat.add_succ_sub_one]))
      (add norm 0 (by grind only [tsub_tsub]))
      (add norm 0 (by grind only [add_tsub_assoc_of_le]))
      (add norm 0 (by grind only [tsub_add_eq_tsub_tsub]))
      (add norm 0 (by grind only [Nat.sub_self]))
      (add norm 0 (by grind only [tsub_tsub_assoc]))
      (add norm 0 (by grind only [tsub_add_tsub_cancel]))
      (add norm 0 (by grind only [Nat.sub_right_comm]))
      (add norm 0 (by grind only [Fintype.card_finset]))

  -- Step 4: Substitute m = n + 2 into m * n = 288.
  have h_step4 : (n + 2) * n = 288 := by
    clear * - h₃ h_step3
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
      (add norm 0 (by bound))
      (add norm 0 (by split))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Nat.mul_succ]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Nat.div_add_mod]))
      (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add norm 0 (by grind only [Nat.mul_add]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
      (add norm 0 (by grind only [Nat.succ_eq_add_one]))
      (add norm 0 (by grind only [Nat.add_sub_cancel]))
      (add norm 0 (by grind only [Nat.fib_add]))
      (add norm 0 (by grind only [Nat.add_comm]))
      (add norm 0 (by grind only [Finset.mulETransformRight.card]))
      (add norm 0 (by grind only [Nat.mul_one]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Nat.add_succ]))
      (add norm 0 (by grind only [Nat.mul_two]))
      (add norm 0 (by grind only [SimpleGraph.Walk.length_append]))
      (add norm 0 (by grind only [Nat.succ_add_sub_one]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [Num.cast_add]))
      (add norm 0 (by grind only [Nat.mod_add_div]))
      (add norm 0 (by rw [mul_self]))

  -- Step 5: Expand (n + 2) * n to n^2 + 2*n.
  have h_step5 : n * n + 2 * n = 288 := by
    clear * - h_step4
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
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Nat.mul_two]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf']))
      (add norm 0 (by grind only [Nat.fib_two_mul]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [Finset.mulETransformRight.card]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by rw [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Nat.mul_succ]))
      (add norm 0 (by grind only [Sym2.two_mul_card_image_offDiag]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [Ring.multichoose_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))

  -- Step 6: We need to solve for n. The informal proof solves n^2 + 2n - 288 = 0 over reals/integers.
  -- For natural numbers, we can just check possible values or use algebraic manipulation.
  -- Let's cast to integers to perform easier algebraic manipulations similar to the informal proof.
  have h_step6 : ((n : ℤ)^2 + 2 * (n : ℤ) : ℤ) = 288 := by
    clear * - h_step5
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by field_simp [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [Nat.cast_ofNat]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Polynomial.derivative_sq]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add norm 0 (by grind only [Int.two_pow_two_pow_add_two_pow_two_pow]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
      (add norm 0 (by grind only [even_two_mul]))
      (add norm 0 (by grind only [Surreal.nsmul_pow_two_powHalf]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [Complex.cpow_two] at *))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 90% (by simp only [ENNReal.rpow_two] at *))

  -- Step 7: Solve the quadratic equation z^2 + 2z - 288 = 0 for integer z = n.
  -- The roots are (-2 +/- sqrt(4 + 1152))/2 = (-2 +/- sqrt(1156))/2 = (-2 +/- 34)/2.
  -- Roots are 16 and -18.
  -- Since n is a natural number, n must be 16.

  -- Let's establish that n satisfies the polynomial equation over integers.
  have h_poly : (n : ℤ)^2 + 2 * (n : ℤ) - 288 = 0 := by
    clear * - h_step6
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
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [div_eq_iff_eq_mul]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [Complex.cpow_two]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add norm 0 (by grind only [Real.rpow_two]))
      (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))

  -- Factorize or use the root finding logic.
  -- (n - 16)(n + 18) = n^2 + 2n - 288.
  have h_factor : (n : ℤ) * (n : ℤ) + 2 * (n : ℤ) - 288 = ((n : ℤ) - 16) * ((n : ℤ) + 18) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxNormIterations := 320
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
      (add norm 0 (by grind only [div_mul]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [gosperCatalan]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [eq_div_iff_mul_eq]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [eq_div_iff_mul_eq']))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by grind only [QuaternionGroup.xa_mul_xa]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [Complex.GammaSeq]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [Real.cos_add_cos]))
      (add norm 0 (by grind only [mul_div_right_comm]))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 1 (by simp_all only [div_eq_iff_eq_mul]))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [sub_div] at *))

  -- Therefore, (n - 16)(n + 18) = 0.
  have h_prod_zero : ((n : ℤ) - 16) * ((n : ℤ) + 18) = 0 := by
    clear * - h_poly h_factor
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
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
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_eq_iff_eq_mul]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [div_mul]))
      (add norm 0 (by grind only [div_eq_one]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [sq_eq_zero_iff]))
      (add norm 0 (by grind only [div_eq_iff_eq_mul']))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [QuaternionGroup.xa_mul_xa]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [eq_div_iff_mul_eq]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [IsCyclotomicExtension.Rat.Three.lambda_sq]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))

  -- Since integers form an integral domain, one of the factors must be zero.
  have h_root_case : (n : ℤ) = 16 ∨ (n : ℤ) = -18 := by
    clear * - h_prod_zero
    norm_cast at h_prod_zero ⊢ <;> aesop
    norm_cast at * <;> linarith

  -- Since n is a natural number, (n : ℤ) cannot be negative (unless n=0, but 0 != -18).
  -- Actually, casting a natural number to int is always non-negative.
  have h_n_nonneg : (n : ℤ) ≥ 0 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
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
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.cast_zero]))
      (add norm 0 (by grind only [Nat.choose_eq_zero_of_lt]))
      (add norm 0 (by grind only [ENat.coe_zero]))
      (add norm 0 (by grind only [Nat.div_zero]))
      (add norm 0 (by grind only [ZMod.val_zero]))
      (add norm 0 (by grind only [Nat.bot_eq_zero]))
      (add norm 0 (by grind only [Nat.totient_zero]))
      (add norm 0 (by grind only [ascPochhammer_eval_zero]))
      (add norm 0 (by grind only [Nat.mul_zero]))
      (add norm 0 (by grind only [Num.cast_zero]))
      (add norm 0 (by grind only [ONote.NF.zero]))
      (add norm 0 (by grind only [ArithmeticFunction.zero_apply]))
      (add norm 0 (by grind only [Nat.choose_eq_zero_iff]))
      (add norm 0 (by grind only [jacobiSym.zero_left]))
      (add norm 0 (by grind only [descPochhammer_eval_zero]))
      (add norm 0 (by grind only [Nat.zero_mul]))
      (add norm 0 (by grind only [zero_tsub]))
      (add norm 0 (by grind only [Nat.dvd_zero]))
      (add norm 0 (by grind only [Nat.digits_zero_succ']))
      (add norm 0 (by grind only [Nat.floor_zero]))
      (add norm 0 (by grind only [Nat.zero_div]))
      (add norm 0 (by grind only [Nat.cast_eq_zero]))
      (add norm 0 (by grind only [Nat.floor_of_nonpos]))
      (add norm 0 (by grind only [ONote.ofNat_zero]))
      (add norm 0 (by grind only [Nat.coprime_zero_right]))
      (add norm 0 (by grind only [Nat.zero_dvd]))
      (add norm 0 (by grind only [Set.ncard_empty]))
      (add norm 0 (by grind only [Nat.zero_shiftLeft]))
      (add norm 0 (by grind only [Nat.cast_choose]))
      (add norm 0 (by grind only [Nat.zero_sub]))
      (add norm 0 (by grind only [Nat.lcm_zero_left]))
      (add norm 0 (by grind only [Nat.digits_zero_zero]))

  -- Thus, n cannot be -18.
  have h_n_not_neg : ¬((n : ℤ) = -18) := by
    clear * - h_n_nonneg
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add norm 0 (by grind only [Nat.cast_ne_zero]))
      (add norm 0 (by grind only [Nat.cast_inj]))
      (add norm 0 (by grind only [Nat.cast_eq_zero]))
      (add norm 0 (by rw [Nat.cast_one]))
      (add norm 0 (by grind only [Nat.cast_eq_one]))
      (add norm 0 (by grind only [ZMod.eq_zero_iff_even]))
      (add norm 0 (by grind only [CharP.cast_eq_zero_iff]))
      (add norm 0 (by rw [Nat.cast_pow]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [Nat.cast_add]))
      (add norm 0 (by grind only [Finset.prod_natCast]))
      (add norm 0 (by grind only [ZMod.natCast_zmod_eq_zero_iff_dvd]))
      (add norm 0 (by rw [Nat.cast_npow]))
      (add norm 0 (by rw [Quaternion.coe_natCast]))
      (add norm 0 (by grind only [Nat.cast_lt]))
      (add norm 0 (by grind only [Nat.Prime.ne_one]))
      (add norm 0 (by grind only [ne_of_gt]))
      (add norm 0 (by grind only [Nat.cast_pos]))
      (add norm 0 (by grind only [mt]))
      (add norm 0 (by grind only [Nat.cast_sum]))
      (add norm 0 (by grind only [padicNorm.nat_eq_one_iff]))
      (add norm 0 (by grind only [Nat.cast_prod]))
      (add norm 0 (by grind only [LT.lt.ne']))
      (add norm 0 (by rw [QuaternionAlgebra.coe_natCast]))
      (add norm 0 (by grind only [Rat.cast_natCast]))
      (add norm 0 (by grind only [ne_of_eq_of_ne]))
      (add norm 0 (by grind only [mul_right_inj']))
      (add norm 0 (by grind only [Int.cast_eq_zero]))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
      (add safe 0 (by simp_all [Int.cast_inj]))
      (add unsafe 50% (by rw [← Int.natCast_inj] at *))
      (add unsafe 50% (by rw [← Int.ofNat_inj] at *))

  -- Therefore, n must be 16.
  have h_n_val : (n : ℤ) = 16 := by
    clear * - h_root_case h_n_not_neg
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
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
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_self_eq_one_iff]))
      (add norm 0 (by grind only [quadraticChar_dichotomy]))
      (add norm 0 (by grind only [quadratic_eq_zero_iff]))
      (add norm 0 (by grind only [eq_inv_iff_mul_eq_one]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [legendreSym.eq_one_or_neg_one]))
      (add norm 0 (by grind only [Quaternion.star_eq_neg]))
      (add norm 0 (by grind only [ValuationSubring.mem_or_inv_mem]))
      (add norm 0 (by grind only [eq_neg_self_iff]))
      (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero_z]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_eq_or]))
      (add norm 0 (by grind only [Int.isUnit_eq_one_or]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_eq_neg]))
      (add norm 0 (by grind only [integral_rpow]))
      (add norm 0 (by grind only [Pell.Solution₁.eq_one_or_neg_one_iff_y_eq_zero]))
      (add norm 0 (by grind only [mul_eq_one_iff_eq_inv]))
      (add norm 0 (by grind only [SzemerediRegularity.card_eq_of_mem_parts_chunk]))
      (add norm 0 (by grind only [inv_eq_one]))
      (add norm 0 (by grind only [Or.resolve_left]))
      (add norm 0 (by grind only [one_eq_inv]))
      (add norm 0 (by grind only [inv_eq_iff_eq_inv]))
      (add unsafe 10% (by grind only [Or]))
      (add unsafe 10% (by grind only [Or.elim]))
      (add unsafe 10% (by grind only [SimpleGraph.Walk.IsEulerian.card_filter_odd_degree]))
      (add unsafe 10% (by grind only [Or.imp]))
      (add unsafe 10% (by grind only [FiniteInter.finiteInterClosure_insert]))
      (add unsafe 10% (by grind only [DirichletCharacter.even_or_odd]))
      (add unsafe 10% (by grind only [Beatty.hit_or_miss']))
      (add unsafe 10% (by grind only [And]))
      (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_lt]))
      (add unsafe 10% (by grind only [Beatty.hit_or_miss]))
      (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_gt]))

  -- Convert back to natural number equality.
  have h_n_nat : n = 16 := by
    clear * - h_n_val
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [ZMod.natCast_zmod_val]))
      (add norm 0 (by rw [Nat.cast_pow]))
      (add norm 0 (by grind only [ZMod.val_cast_of_lt]))
      (add norm 0 (by rw [Nat.cast_npow]))
      (add norm 0 (by grind only [ZMod.val]))
      (add norm 0 (by grind only [ZMod.val_natCast]))
      (add norm 0 (by grind only [ZMod.natCast_zmod_eq_zero_iff_dvd]))
      (add norm 0 (by grind only [ZMod.val_one]))
      (add norm 0 (by grind only [CharP.cast_eq_zero_iff]))
      (add norm 0 (by grind only [ZMod.eq_iff_modEq_nat]))
      (add norm 0 (by rw [Nat.cast_one]))
      (add norm 0 (by rw [ZMod.natCast_eq_natCast_iff]))
      (add norm 0 (by rw [ZMod]))
      (add norm 0 (by rw [QuaternionAlgebra.coe_natCast]))
      (add norm 0 (by rw [ZMod.natCast_self]))
      (add norm 0 (by grind only [ZMod.eq_zero_iff_even]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by rw [ZMod.natCast_val]))
      (add norm 0 (by rw [Quaternion.coe_natCast]))
      (add norm 0 (by grind only [Nat.cast_ne_zero]))
      (add norm 0 (by rw [ZMod.natCast_mod]))
      (add norm 0 (by grind only [padicNorm.nat_eq_one_iff]))
      (add norm 0 (by rw [ZMod.intCast_zmod_eq_zero_iff_dvd]))
      (add norm 0 (by rw [Int.natCast_modEq_iff]))
      (add norm 0 (by rw [PNat.val_ofNat]))
      (add norm 0 (by rw [Nat.cast_ofNat]))
      (add norm 0 (by grind only [ZMod.val_eq_zero]))
      (add safe 1 (by simp_all only [Finset.prod_natCast]))
      (add unsafe 50% (by rw [← Nat.cast_inj] at *))
      (add unsafe 50% (by rw [← Int.natCast_inj] at *))
      (add unsafe 50% (by rw [← Int.natAbs_ofNat] at *))
      (add unsafe 50% (by rw [← Int.ofNat_inj] at *))

  -- Step 12: Calculate m using m = n + 2.
  have h_m_calc : m = 16 + 2 := by
    clear * - h_step3 h_n_nat
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [Nat.mul_one]))
      (add norm 0 (by grind only [goldenRatio]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by rw [Nat.cast_one]))
      (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by rw [Nat.factorial_one]))
      (add norm 0 (by grind only [Pell.xn_succ_succ]))
      (add norm 0 (by rw [Nat.cast_add]))
      (add norm 0 (by grind only [add_idem]))
      (add norm 0 (by grind only [numDerangements_add_two]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Nat.one_add]))
      (add norm 0 (by rw [Nat.cast_ofNat]))
      (add norm 0 (by grind only [Nat.mul_succ]))
      (add norm 0 (by grind only [Nat.factorial_succ]))
      (add norm 0 (by grind only [even_two]))
      (add norm 0 (by grind only [Nat.succ_add_sub_one]))
      (add norm 0 (by grind only [gold_sq]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [ArithmeticFunction.one_apply]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by rw [ArithmeticFunction.natCoe_one]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by rw [Int.ofNat_add]))
      (add norm 0 (by grind only [Num.cast_succ]))

  -- Step 13: Simplify 16 + 2 to 18.
  have h_m_val : m = 18 := by
    clear * - h_m_calc
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
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
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_left_eq_self]))
      (add norm 0 (by grind only [Polynomial.IsUnitTrinomial.irreducible_aux2]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [mul_right_eq_self]))
      (add norm 0 (by grind only [Polynomial.IsUnitTrinomial.irreducible_aux3]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [self_eq_mul_left]))
      (add norm 0 (by grind only [sq_eq_sq_iff_eq_or_eq_neg]))
      (add norm 0 (by grind only [mul_self_eq_one_iff]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [mul_eq_one_iff']))
      (add norm 0 (by grind only [Zsqrtd.not_divides_sq]))
      (add norm 0 (by grind only [Polynomial.mirror_inj]))
      (add norm 0 (by grind only [mul_eq_left₀]))
      (add norm 0 (by grind only [Polynomial.mirror_eq_iff]))
      (add norm 0 (by grind only [eq_inv_iff_mul_eq_one]))
      (add norm 0 (by grind only [inv_eq_iff_mul_eq_one]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [self_eq_mul_right]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Nat.prime_two]))
      (add norm 0 (by grind only [primorial_succ]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Or.resolve_left]))
      (add norm 0 (by grind only [mul_left_inj']))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add unsafe 10% (by grind only [mul_left_cancel₀]))
      (add unsafe 10% (by grind only [mul_right_inj']))
      (add unsafe 90% (by simp only [pow_two] at *))

  exact h_m_val
