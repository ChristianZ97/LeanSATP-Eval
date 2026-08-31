
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

theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k ∈ Finset.range 8, (2 * k + 1)) - ↑(∑ k ∈ Finset.range 5, (a + 2 * k)) = (4 : ℤ)) :
    a = 8 := by
  -- Step 1 & 2: Sum of first 8 odd numbers is 64
  have h_sum_odd : (∑ k ∈ Finset.range 8, (2 * k + 1)) = 64 := by
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
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by ring_nf at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Finset.prod_range_succ_comm]))
      (add norm 0 (by grind only [Nat.choose_self]))
      (add norm 0 (by grind only [Finset.prod_range_one]))
      (add norm 0 (by grind only [Finset.prod_range_zero]))
      (add norm 0 (by grind only [Finset.range_add_one]))
      (add norm 0 (by grind only [Nat.prod_range_factorial_succ]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [Finset.range_succ]))
      (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
      (add norm 0 (by grind only [Nat.choose_zero_right]))
      (add norm 0 (by grind only [Nat.choose_one_right]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [Nat.prod_range_succ_factorial]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [Nat.choose_succ_self_right]))
      (add norm 0 (by grind only [sum_range_pow]))
      (add norm 0 (by grind only [Nat.factorial]))
      (add norm 0 (by grind only [numDerangements]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Polynomial.sum_bernoulli]))
      (add norm 0 (by grind only [bernsteinPolynomial.sum]))
      (add norm 0 (by grind only [Finset.prod_flip]))
      (add norm 0 (by grind only [Finset.range_zero]))
      (add norm 0 (by grind only [geom_sum_mul_add]))
      (add norm 0 (by grind only [intervalIntegral.sum_integral_adjacent_intervals]))
      (add norm 0 (by grind only [WittVector.frobeniusPolyAux_eq]))
      (add norm 0 (by grind only [add_pow]))
      (add norm 0 (by grind only [Finset.prod_range_induction]))
      (add norm 0 (by grind only [Finset.Nat.prod_antidiagonal_eq_prod_range_succ]))
      (add safe 0 (by simp only [Finset.range_one] at *))

  -- Step 3, 4, 5: Expand sum (a + 2k) for k=0 to 4 -> 5a + 20
  have h_sum_even_expr : (∑ k ∈ Finset.range 5, (a + 2 * k)) = 5 * a + 20 := by
    clear * -
    have : (0 : ℕ) < 5 := by decide
    have h₁ := this
    on_goal 1 => simp [Finset.sum_range_succ] <;> ring

  -- Step 6, 7, 8: Substitute into h1
  -- h1 says: sum_odd - sum_even = 4
  -- which means: 64 - (5a + 20) = 4
  have h_eq_subst : ((64 : ℤ) - ↑(5 * a + 20)) = (4 : ℤ) := by
    clear * - h_sum_odd h_sum_even_expr h₁
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by rfl))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [Nat.cast_add]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [Nat.cast_succ]))
      (add norm 0 (by rw [Nat.cast_one]))
      (add norm 0 (by grind only [Nat.cast_sub]))
      (add norm 0 (by grind only [Nat.cast_add_choose]))
      (add norm 0 (by rw [Int.ofNat_add]))
      (add norm 0 (by grind only [Nat.factorial_succ]))
      (add norm 0 (by rw [QuaternionAlgebra.coe_natCast]))
      (add norm 0 (by grind only [numDerangements_succ]))
      (add norm 0 (by grind only [Nat.cast_add_one]))
      (add norm 0 (by grind only [Num.cast_succ]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by rw [Nat.cast_inj]))
      (add norm 0 (by rw [Complex.logTaylor_succ]))
      (add norm 0 (by rw [Finset.prod_natCast]))
      (add norm 0 (by grind only [Nat.cast_sum]))
      (add norm 0 (by grind only [Complex.Gamma_nat_eq_factorial]))
      (add norm 0 (by rw [Quaternion.coe_natCast]))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [div_eq_iff_eq_mul]))
      (add norm 0 (by rw [Nat.cast_id]))
      (add norm 0 (by grind only [Pell.x_sub_y_dvd_pow]))
      (add norm 0 (by grind only [Num.cast_succ']))
      (add norm 0 (by grind only [Nat.factorial]))
      (add norm 0 (by rw [Nat.cast_ofNat]))
      (add norm 0 (by grind only [Polynomial.natCast_mul]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [Nat.succ_sub_one]))
      (add norm 0 (by rw [ZNum.of_natCast]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by rw [ZMod.natCast_zmod_val]))

  -- Step 9, 10, 11: Solve for a
  -- 64 - 5a - 20 = 4
  -- 44 - 5a = 4
  -- 40 = 5a
  -- a = 8

  -- Let's break down the algebraic manipulation more carefully for Lean
  have h_simplify_1 : ((64 : ℤ) - 20) - ↑(5 * a) = (4 : ℤ) := by
    clear * - h_eq_subst
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      enableSimp := false
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
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [eq_div_iff_mul_eq]))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by grind only [LucasLehmer.Int.coe_nat_two_pow_pred]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux4]))
      (add norm 0 (by grind only [gosperCatalan]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Complex.sin_two_mul]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add safe 1 (by simp_all only [div_eq_iff_eq_mul]))
      (add safe 1 (by apply div_mul))
      (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))

  have h_simplify_2 : (44 : ℤ) - ↑(5 * a) = (4 : ℤ) := by
    clear * - h_simplify_1
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 20
      maxNormIterations := 520
      enableSimp := false
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
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux4]))
      (add norm 0 (by grind only [Iff]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [div_eq_iff_eq_mul]))
      (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Complex.sin_two_mul]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [FractionalIdeal.mem_div_iff_of_nonzero]))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [div_mul] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add unsafe 10% (by grind only [zero_lt_two]))
      (add unsafe 10% (by grind only [mul_lt_mul_left]))
      (add unsafe 10% (by grind only [mul_nonneg_iff_of_pos_right]))
      (add unsafe 10% (by grind only [mul_lt_mul_right]))
      (add unsafe 10% (by grind only [mul_left_cancel₀]))
      (add unsafe 10% (by grind only [LucasLehmer.Int.coe_nat_two_pow_pred]))

  have h_simplify_3 : ↑(5 * a) = (40 : ℤ) := by
    clear * - h_simplify_2
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
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
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [IsPGroup.commutative_of_card_eq_prime_sq]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [nat_mul_inj']))
      (add norm 0 (by grind only [Eq.symm]))
      (add norm 0 (by grind only [Char.card_pow_char_pow]))
      (add norm 0 (by grind only [Nat.factorial_two]))
      (add norm 0 (by grind only [CharTwo.two_eq_zero]))
      (add norm 0 (by grind only [eq_mul_of_div_eq']))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [InnerProductSpaceable]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [mul_comm_of_exponent_two]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [HurwitzZeta.hurwitzZetaEven_neg_two_mul_nat_add_one]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [quadraticChar_sq_one']))
      (add norm 0 (by grind only [Eq.trans]))
      (add unsafe 10% (by grind only [mul_left_cancel₀]))
      (add unsafe 10% (by grind only [eq_div_iff_mul_eq]))
      (add unsafe 10% (by grind only [mul_right_inj']))
      (add unsafe 10% (by grind only [sq_ne_two_fin_zmod_four]))
      (add unsafe 10% (by grind only [Int.cast_ofNat]))
      (add unsafe 10% (by grind only [DihedralGroup.div_two_lt]))
      (add unsafe 10% (by grind only [Nat.cast_ofNat]))
      (add unsafe 10% (by grind only [Polynomial.IsUnitTrinomial.irreducible_aux2]))
      (add unsafe 10% (by grind only [LucasLehmer.Int.coe_nat_two_pow_pred]))
      (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
      (add unsafe 10% (by grind only [Int.sq_of_gcd_eq_one]))
      (add unsafe 10% (by grind only [qrSign.eq_iff_eq]))

  have h_a_eq_8 : a = 8 := by
    clear * - h_simplify_3
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [nat_mul_inj]))
      (add norm 0 (by grind only [nat_mul_inj']))
      (add norm 0 (by grind only [mul_left_inj']))
      (add norm 0 (by grind only [Nat.mul_right_inj]))
      (add norm 0 (by grind only [qrSign.eq_iff_eq]))
      (add norm 0 (by grind only [mul_eq_mul_left_iff]))
      (add norm 0 (by grind only [sq_ne_two_fin_zmod_four]))
      (add norm 0 (by grind only [mul_comm_of_exponent_two]))
      (add norm 0 (by grind only [Polynomial.IsUnitTrinomial.irreducible_aux2]))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 0 (by grind only [sq_eq_sq_iff_eq_or_eq_neg]))
      (add norm 0 (by grind only [DihedralGroup.div_two_lt]))
      (add norm 0 (by grind only [IsPGroup.commutative_of_card_eq_prime_sq]))
      (add norm 0 (by grind only [mul_eq_left₀]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Ordinal.mul_right_inj]))
      (add norm 0 (by grind only [eq_or_eq_neg_of_sq_eq_sq]))
      (add norm 0 (by grind only [Polynomial.IsUnitTrinomial.irreducible_aux3]))
      (add norm 0 (by grind only [Nat.mul_left_cancel]))
      (add norm 0 (by grind only [mul_left_cancel]))
      (add norm 0 (by grind only [mul_left_cancel_iff_of_pos]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Nat.exists_eq_pow_mul_and_not_dvd]))
      (add norm 0 (by grind only [Nat.cast_ofNat]))
      (add norm 0 (by grind only [mul_left_eq_self]))
      (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
      (add norm 0 (by grind only [Nat.sq_add_sq_mul]))
      (add norm 0 (by grind only [Num.of_nat_inj]))
      (add unsafe 10% (by grind only [mul_left_cancel₀]))
      (add unsafe 10% (by grind only [mul_right_inj']))
      (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))

  exact h_a_eq_8
