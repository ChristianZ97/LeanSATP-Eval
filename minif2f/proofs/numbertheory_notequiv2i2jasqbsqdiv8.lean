
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

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  -- Step 3 & 4: Define specific counterexample values
  let a_val : ℤ := 2
  let b_val : ℤ := 0
  -- Step 5-8: Prove P(2, 0) is true
  have hP_true : (∃ i j : ℤ, a_val = 2 * i ∧ b_val = 2 * j) := by
    have h_i : a_val = 2 * 1 := by norm_num [a_val]
    have h_j : b_val = 2 * 0 := by norm_num [b_val]
    exact ⟨1, 0, by norm_num [a_val], by norm_num [b_val]⟩

  -- Step 9-13: Prove Q(2, 0) is false
  have hQ_false : ¬(∃ k : ℤ, a_val ^ 2 + b_val ^ 2 = 8 * k) := by
    intro h_ex_k
    rcases h_ex_k with ⟨k, hk⟩
    -- a^2 + b^2 = 2^2 + 0^2 = 4
    have h_eq : a_val ^ 2 + b_val ^ 2 = 4 := by norm_num [a_val, b_val]
    rw [h_eq] at hk
    -- 4 = 8 * k implies k = 1/2, which is not an integer
    have h_k_ne_int : k ≠ 1 / 2 := by
      -- In integers, 8*k = 4 has no solution because 4 is not divisible by 8
      have h_div : 8 * k = 4 := by linarith
      have h_impossible : False := by
        -- If 8*k = 4 in integers, then k must be such that 8 divides 4, which is false
        -- Alternatively, consider modulo 8 or simply check possible integer values
        have h_k_bound : k ≤ 0 ∨ k ≥ 1 := by
          by_cases hk_pos : k > 0
          · right; omega
          · left; omega

        aesop (config := {
          maxRuleApplications := 100
          maxRuleApplicationDepth := 10
          maxNormIterations := 320
          })
          (add norm 100 (by norm_cast))
          (add norm 0 (by linarith))
          (add norm 0 (by nlinarith))
          (add norm 0 (by positivity))
          (add norm 1 (by push_neg))
          (add norm 0 (by bound))
          (add norm 1 (by ext))
          (add norm 1 (by field_simp [*] at *))
          (add safe 100 (by ring))
          (add safe 100 (by field_simp))
          (add safe 100 (by norm_num))
          (add safe 100 (by omega))
          (add safe 0 (by gcongr))
          (add safe 100 (by interval_cases))
          (add safe 0 (by split))
          (add safe 100 (by norm_cast at *))
          (add safe 100 (by decide))
          (add safe 100 (by assumption_mod_cast))
          (add norm 0 (by grind only [Int.le_self_sq]))
          (add norm 0 (by grind only [sq_nonneg]))
          (add norm 0 (by grind only [sq_le_sq]))
          (add norm 0 (by grind only [sq_pos_of_pos]))
          (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
          (add norm 0 (by grind only [one_le_sq_iff]))
          (add norm 0 (by grind only [Real.le_sqrt]))
          (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
          (add norm 0 (by grind only [zero_le_two]))
          (add norm 0 (by grind only [mul_self_nonneg]))
          (add norm 0 (by grind only [Real.le_sqrt']))
          (add norm 0 (by grind only [le_mul_of_one_le_left']))
          (add norm 0 (by grind only [Real.sqrt_le_left]))
          (add norm 0 (by grind only [two_mul_le_add_sq]))
          (add unsafe 10% (by grind only [mul_le_mul_right]))
          (add unsafe 10% (by grind only [EisensteinSeries.div_max_sq_ge_one]))
          (add unsafe 10% (by grind only [mul_nonneg_iff_of_pos_right]))
          (add unsafe 10% (by grind only [mul_le_mul_left]))
          (add unsafe 10% (by grind only [Nat.cast_nonneg]))
          (add unsafe 10% (by grind only [zero_lt_two]))
          (add unsafe 10% (by grind only [Pell.IsFundamental.x_le_x]))
          (add unsafe 10% (by grind only [le_of_mul_le_mul_right]))
          (add unsafe 10% (by grind only [le_of_mul_le_mul_left]))
          (add unsafe 10% (by grind only [mul_le_iff_le_one_left]))
          (add unsafe 10% (by grind only [And]))
          (add unsafe 10% (by grind only [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
          (add unsafe 10% (by grind only [GeneralizedContinuedFraction.IntFractPair.nth_stream_fr_nonneg]))
          (add unsafe 10% (by grind only [mul_nonneg_iff_of_pos_left]))
          (add unsafe 10% (by grind only [Or.elim]))
          (add unsafe 10% (by grind only [SzemerediRegularity.seven_le_initialBound]))
          (add unsafe 10% (by grind only [Or.resolve_left]))
          (add unsafe 10% (by grind only [le_or_lt]))

      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 10
        maxNormIterations := 520
        maxGoals := 256
        useDefaultSimpSet := false
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
        (add safe 0 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [irrational_iff_ne_rational]))
        (add norm 0 (by grind only [mt]))
        (add norm 0 (by grind only [two_ne_zero]))
        (add norm 0 (by grind only [Iff]))
        (add norm 0 (by grind only [mul_ne_zero]))
        (add norm 0 (by grind only [zero_lt_two]))
        (add norm 0 (by grind only [div_ne_one]))
        (add norm 0 (by grind only [LT.lt.ne']))
        (add norm 0 (by grind only [Int.cast_ne_zero]))
        (add norm 0 (by grind only [pow_ne_zero]))
        (add norm 0 (by grind only [EisensteinSeries.div_max_sq_ge_one]))
        (add norm 0 (by grind only [sq_eq_zero_iff]))
        (add norm 0 (by grind only [div_ne_one_of_ne]))
        (add norm 0 (by grind only [LucasLehmer.mersenne_int_ne_zero]))
        (add norm 0 (by grind only [sq_pos_of_pos]))
        (add norm 0 (by grind only [Int.sq_of_gcd_eq_one]))
        (add norm 0 (by grind only [Zsqrtd.norm_eq_zero]))
        (add norm 0 (by grind only [Ne]))
        (add norm 0 (by grind only [Or.resolve_right]))
        (add norm 0 (by grind only [Irrational.ne_int]))
        (add norm 0 (by grind only [Ne.symm]))
        (add norm 0 (by grind only [mul_eq_zero]))
        (add norm 0 (by grind only [div_eq_zero_iff]))
        (add norm 0 (by grind only [mul_nonneg_iff_of_pos_right]))
        (add norm 0 (by grind only [ne_of_lt]))
        (add norm 0 (by grind only [ne_of_eq_of_ne]))
        (add norm 0 (by grind only [GaussianInt.toComplex_eq_zero]))
        (add norm 0 (by grind only [Zsqrtd.norm_eq_zero_iff]))
        (add norm 0 (by grind only [Function.Injective.ne]))
        (add safe 0 (by simp only [div_ne_zero] at *))
        (add unsafe 10% (by grind only [ne_of_gt]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_left]))

    -- Since k is an integer, it cannot satisfy 8*k=4
    have h_not_solvable : False := by
      apply h_k_ne_int.symm
      -- We need to show that if 8*k=4, then k would effectively be 1/2, but k is int
      -- Actually, simpler logic: just show no integer k satisfies 8*k=4
      have h_8k_eq_4 : 8 * k = 4 := by linarith
      -- Check all possibilities for small k or use divisibility
      -- 8 divides 4 is false in Z
      have h_false : False := by
        omega

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
        (add norm 0 (by omega))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 1 (by field_simp [*] at *))
        (add norm 1 (by norm_num [*] at *))
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
        (add norm 0 (by grind only [two_ne_zero]))
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [zero_lt_two]))
        (add norm 0 (by grind only [Nat.cast_two]))
        (add norm 0 (by grind only [two_ne_zero']))
        (add norm 0 (by grind only [eq_div_iff_mul_eq]))
        (add norm 0 (by grind only [Int.cast_ofNat]))
        (add norm 0 (by grind only [Eq.symm]))
        (add norm 0 (by grind only [mul_two]))
        (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
        (add norm 0 (by grind only [Int.cast_two]))
        (add norm 0 (by grind only [CharTwo.two_eq_zero]))
        (add norm 0 (by grind only [gaussSum_sq]))
        (add norm 0 (by grind only [Nat.cast_descFactorial_two]))
        (add norm 0 (by grind only [even_two]))
        (add norm 0 (by grind only [pow_two]))
        (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
        (add norm 0 (by grind only [Real.Gamma_two]))
        (add norm 0 (by grind only [Int.sq_of_gcd_eq_one]))
        (add norm 0 (by grind only [Quaternion.self_add_star]))
        (add norm 0 (by grind only [Nat.factorial_two]))
        (add norm 0 (by grind only [zero_lt_two']))
        (add norm 0 (by grind only [Nat.cast_ofNat]))
        (add norm 0 (by grind only [Quaternion.star_add_self]))
        (add norm 0 (by grind only [mul_right_inj']))
        (add norm 0 (by grind only [mul_left_cancel₀]))
        (add safe 0 (by simp only [eq_div_iff] at *))
        (add safe 0 (by simp only [div_eq_iff] at *))
        (add unsafe 10% (by grind only [div_eq_iff_mul_eq]))
        (add unsafe 50% (by rw [← Int.ofNat_inj] at *))
        (add unsafe 50% (by rw [← Int.natCast_inj] at *))
        (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))

    exact h_not_solvable

  -- Step 14-15: P(2,0) <-> Q(2,0) is false
  have h_biconditional_false : ¬((∃ i j : ℤ, a_val = 2 * i ∧ b_val = 2 * j) ↔ ∃ k : ℤ, a_val ^ 2 + b_val ^ 2 = 8 * k) := by
    intro h_equiv
    -- If they are equivalent, and LHS is true, RHS must be true
    have h_rhs_true : ∃ k : ℤ, a_val ^ 2 + b_val ^ 2 = 8 * k := by
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        enableUnfold := false
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
        (add safe 0 (by positivity))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [zero_lt_two]))
        (add norm 0 (by grind only [Nat.cast_two]))
        (add norm 0 (by grind only [two_ne_zero]))
        (add norm 0 (by grind only [gaussSum_sq]))
        (add norm 0 (by grind only [Int.cast_ofNat]))
        (add norm 0 (by grind only [QuaternionGroup.xa_sq]))
        (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
        (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
        (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
        (add norm 0 (by grind only [even_iff_two_dvd]))
        (add norm 0 (by grind only [Char.card_pow_char_pow]))
        (add norm 0 (by grind only [Nat.cast_ofNat]))
        (add norm 0 (by grind only [Int.isUnit_sq]))
        (add norm 0 (by grind only [GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible]))
        (add norm 0 (by grind only [mul_two]))
        (add norm 0 (by grind only [CharTwo.two_eq_zero]))
        (add norm 0 (by grind only [Odd]))
        (add norm 0 (by grind only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
        (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
        (add norm 0 (by grind only [Nat.prime_two]))
        (add norm 0 (by grind only [euler_four_squares]))
        (add norm 0 (by grind only [Nat.sq_add_sq_mul]))
        (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
        (add norm 0 (by grind only [Int.sq_of_gcd_eq_one]))
        (add norm 0 (by grind only [Quaternion.self_add_star]))
        (add norm 0 (by grind only [mul_pow]))
        (add norm 0 (by grind only [ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime]))
        (add norm 0 (by grind only [ZMod.sq_add_sq]))
        (add unsafe 90% (by simp only [pow_two] at *))
        (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
        (add unsafe 50% (by simp only [sq_add_sq_mul]))

    exact hQ_false h_rhs_true

  -- Step 16-20: Construct the final proof of negation
  have h_main : ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
    intro h_forall
    -- Apply forall to our specific a and b
    have h_ab_equiv : (∃ i j : ℤ, a_val = 2 * i ∧ b_val = 2 * j) ↔ ∃ k : ℤ, a_val ^ 2 + b_val ^ 2 = 8 * k := h_forall a_val b_val
    exact h_biconditional_false h_ab_equiv

  exact h_main
