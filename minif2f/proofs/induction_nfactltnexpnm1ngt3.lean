
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

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  -- Step 1: Base case for n = 3
  have h_base : 3 ! < 3 ^ (3 - 1) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by norm_num))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 1 (by simp_all [lt_mul_iff_one_lt_left']))
      (add norm 1 (by simp_all [lt_mul_of_one_lt_left']))
      (add norm 0 (by grind only [mabs_lt]))
      (add unsafe 50% (by simp only [Real.sqrt_lt]))
      (add unsafe 50% (by nlinarith [inv_lt]))
      (add unsafe 50% (by nlinarith [inv_lt_inv]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_iff_lt_rpow]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_iff_lt_rpow_of_base_lt_one]))
      (add unsafe 50% (by nlinarith [Real.log_lt_log_iff]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_logb_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [lt_inv]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left]))
      (add unsafe 50% (by nlinarith [Real.sqrt_lt']))
      (add unsafe 50% (by nlinarith [Real.logb_lt_logb]))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 10% (by grind only [zero_lt_two]))
      (add unsafe 50% (by nlinarith [pow_lt_one]))
      (add unsafe 50% (by nlinarith [lt_div_iff']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [div_lt_iff']))
      (add unsafe 50% (by nlinarith [inv_lt']))
      (add unsafe 50% (by nlinarith [Real.log_lt_iff_lt_exp]))
      (add unsafe 50% (by nlinarith [Real.aux₀]))
      (add unsafe 50% (by nlinarith [Real.rpow_lt_rpow]))
      (add unsafe 50% (by nlinarith [div_lt_self_iff]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_logb_iff_of_base_lt_one]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_right]))
      (add unsafe 50% (by nlinarith [Real.lt_rpow_iff_log_lt]))
      (add unsafe 50% (by nlinarith [Real.lt_logb_iff_rpow_lt]))

  -- Induction setup
  induction' h₀ with k hk ih
  · -- Case n = 3
    exact h_base

  · -- Case n = k + 1, where k ≥ 3
    -- Hypothesis: k! < k^(k-1)
    have h_k_fact_lt_pow : k ! < k ^ (k - 1) := ih

    -- Step 3: (k+1)! = (k+1) * k!
    have h_fact_recursion : (k + 1) ! = (k + 1) * k ! := by
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
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 100 (by ring_nf at *))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 0 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Nat.mul_succ]))
        (add norm 0 (by grind only [Nat.mul_add]))
        (add norm 0 (by grind only [Nat.succ_mul]))
        (add norm 0 (by grind only [Nat.mul_comm]))
        (add norm 0 (by grind only [Nat.factorial_succ]))
        (add norm 0 (by grind only [Nat.mul_assoc]))
        (add norm 0 (by grind only [Nat.add_mul]))
        (add norm 0 (by grind only [Nat.mul_one]))
        (add norm 0 (by grind only [Nat.superFactorial_succ]))
        (add norm 0 (by grind only [Nat.mul_left_comm]))
        (add norm 0 (by grind only [Nat.left_distrib]))
        (add norm 0 (by grind only [Nat.mul_right_comm]))
        (add norm 0 (by grind only [Nat.pow_succ]))
        (add norm 0 (by grind only [Nat.factorial_eq_mul_doubleFactorial]))
        (add norm 0 (by grind only [Nat.one_mul]))
        (add norm 0 (by grind only [Nat.succ_mul_succ]))
        (add norm 0 (by grind only [Nat.succ_mul_choose_eq]))
        (add norm 0 (by grind only [Nat.pow_succ']))
        (add norm 0 (by grind only [Nat.superFactorial]))
        (add norm 0 (by grind only [Nat.succ_ascFactorial]))
        (add norm 0 (by grind only [Nat.ascFactorial_succ]))
        (add norm 0 (by grind only [Nat.descFactorial_succ]))
        (add norm 0 (by grind only [Nat.succ_sub_succ]))
        (add norm 0 (by grind only [Nat.pow_add]))
        (add norm 0 (by grind only [Nat.factorial_mul_ascFactorial]))
        (add norm 0 (by grind only [Nat.choose_succ_right_eq]))
        (add norm 0 (by grind only [Nat.add_succ]))
        (add norm 0 (by grind only [Nat.succ_add]))
        (add norm 0 (by grind only [Nat.succ_add_sub_one]))
        (add norm 0 (by grind only [Nat.add_comm]))
        (add norm 0 (by grind only [ZMod.gauss_lemma_aux₁]))
        (add norm 0 (by grind only [Pell.xn_succ]))

    -- Step 4: (k+1)! < (k+1) * k^(k-1)
    have h_step4 : (k + 1) ! < (k + 1) * k ^ (k - 1) := by
      clear * - h_fact_recursion h_k_fact_lt_pow
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        maxGoals := 16
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by positivity))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 100 (by exfalso))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 0 (by omega))
        (add safe 0 (by push_neg))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by norm_cast at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [pow_lt_pow_succ]))
        (add norm 0 (by grind only [Nat.mul_lt_mul_pow_succ]))
        (add norm 0 (by grind only [lt_of_pow_lt_pow_left]))
        (add norm 0 (by grind only [Nat.mul_lt_mul_of_le_of_lt]))
        (add norm 0 (by grind only [Nat.mul_lt_mul_of_lt_of_le']))
        (add norm 0 (by grind only [Nat.mul_lt_mul_of_pos_right]))
        (add norm 0 (by grind only [Nat.succ_mul]))
        (add norm 0 (by grind only [Nat.lt_mul_div_succ]))
        (add norm 0 (by grind only [Monotone.seq_pos_lt_seq_of_lt_of_le]))
        (add norm 0 (by grind only [Nat.succ_pos]))
        (add norm 0 (by grind only [Nat.pow_succ']))
        (add unsafe 10% (by grind only [pow_lt_pow_right]))
        (add unsafe 10% (by grind only [Nat.mul_lt_mul_right]))
        (add unsafe 10% (by grind only [pow_lt_pow_right₀]))
        (add unsafe 10% (by grind only [Nat.mul_lt_mul_of_pos_left]))
        (add unsafe 10% (by grind only [Monotone.seq_pos_lt_seq_of_le_of_lt]))
        (add unsafe 10% (by grind only [Nat.mul_lt_mul_left]))
        (add unsafe 50% (by nlinarith [mul_lt_mul]))
        (add unsafe 10% (by grind only [Nat.sub_lt]))
        (add unsafe 50% (by nlinarith [mul_lt_mul']))
        (add unsafe 50% (by nlinarith [pow_lt_pow_left]))
        (add unsafe 50% (by nlinarith [lt_of_mul_lt_mul_left]))
        (add unsafe 50% (by nlinarith [lt_mul_left]))
        (add unsafe 10% (by grind only [Nat.mul_pos]))
        (add unsafe 50% (by nlinarith [lt_of_mul_lt_mul_right]))
        (add unsafe 10% (by grind only [Nat.lt_of_succ_le]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_left']))
        (add unsafe 10% (by grind only [Pell.eq_pow_of_pell_lem]))
        (add unsafe 50% (by nlinarith [mul_lt_mul₀]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
        (add unsafe 10% (by grind only [Int.lt_of_sum_four_squares_eq_mul]))
        (add unsafe 10% (by grind only [Nat.four_pow_lt_mul_centralBinom]))

    -- Step 5 & 6 implication: Since k >= 3, k < k+1, thus k^(k-1) < (k+1)^(k-1)
    have h_pow_ineq : k ^ (k - 1) < (k + 1) ^ (k - 1) := by
      clear * - hk
      gcongr
      · cases k
        · contradiction
        · simp_all
          omega
      · linarith

    -- Step 7: (k+1) * k^(k-1) < (k+1) * (k+1)^(k-1)
    have h_step7 : (k + 1) * k ^ (k - 1) < (k + 1) * (k + 1) ^ (k - 1) := by
      clear * - h_pow_ineq
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by positivity))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 100 (by exfalso))
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
        (add norm 0 (by grind only [pow_lt_pow_succ]))
        (add norm 0 (by grind only [lt_of_pow_lt_pow_left]))
        (add norm 0 (by grind only [Nat.mul_lt_mul_pow_succ]))
        (add norm 0 (by grind only [Monotone.seq_pos_lt_seq_of_lt_of_le]))
        (add norm 0 (by grind only [Nat.mul_lt_mul_of_pos_right]))
        (add norm 0 (by grind only [Nat.mul_lt_mul_of_le_of_lt]))
        (add norm 0 (by grind only [Nat.mul_lt_mul_of_lt_of_le']))
        (add norm 0 (by grind only [pow_lt_pow_right_of_lt_one]))
        (add unsafe 10% (by grind only [pow_lt_pow_right]))
        (add unsafe 10% (by grind only [pow_lt_pow_right₀]))
        (add unsafe 50% (by nlinarith [mul_lt_mul]))
        (add unsafe 10% (by grind only [pow_lt_pow_left]))
        (add unsafe 50% (by nlinarith [lt_mul_left]))
        (add unsafe 10% (by grind only [Monotone.seq_pos_lt_seq_of_le_of_lt]))
        (add unsafe 10% (by grind only [Nat.mul_lt_mul_of_pos_left]))
        (add unsafe 50% (by nlinarith [mul_lt_mul']))
        (add unsafe 10% (by grind only [lt_of_mul_lt_mul_left]))
        (add unsafe 50% (by nlinarith [lt_of_mul_lt_mul_right]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
        (add unsafe 50% (by nlinarith [mul_lt_mul₀]))
        (add unsafe 50% (by nlinarith [mul_lt_mul'']))
        (add unsafe 10% (by grind only [Nat.mul_lt_mul_right]))
        (add unsafe 50% (by nlinarith [mul_add_mul_lt_mul_add_mul]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_right']))
        (add unsafe 50% (by nlinarith [mul_lt_mul_left']))
        (add unsafe 10% (by grind only [Int.lt_of_sum_four_squares_eq_mul]))
        (add unsafe 50% (by nlinarith [pow_lt_pow_iff_right_of_lt_one]))
        (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left]))
        (add unsafe 10% (by grind only [Nat.sub_lt]))
        (add unsafe 50% (by nlinarith [Real.pi_lt_sqrtTwoAddSeries]))
        (add unsafe 10% (by grind only [Nat.four_pow_lt_mul_centralBinom]))

    -- Step 8: (k+1) * (k+1)^(k-1) = (k+1)^k
    have h_step8 : (k + 1) * (k + 1) ^ (k - 1) = (k + 1) ^ k := by
      clear * -
      cases k <;> simp [Nat.pow_succ, mul_add] <;> ring

    -- Step 9: (k+1)! < (k+1)^k
    have h_step9 : (k + 1) ! < (k + 1) ^ k := by
      clear * - h_step4 h_step7 h_step8
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
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 100 (by exfalso))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Nat.succ_mul]))
        (add norm 0 (by grind only [Nat.pow_succ']))
        (add norm 0 (by grind only [Nat.mul_succ]))
        (add norm 0 (by grind only [Nat.pow_succ]))
        (add norm 0 (by grind only [Nat.succ_sub_succ]))
        (add norm 0 (by grind only [Nat.superFactorial_succ]))
        (add norm 0 (by grind only [Nat.factorial_succ]))
        (add norm 0 (by grind only [Nat.succ_sub_succ_eq_sub]))
        (add norm 0 (by grind only [Nat.succ_pos]))
        (add norm 0 (by grind only [Pell.xn_succ]))
        (add norm 0 (by grind only [pow_succ]))
        (add norm 0 (by grind only [Nat.succ_eq_add_one]))
        (add norm 0 (by grind only [Nat.succ_mul_succ]))
        (add norm 0 (by grind only [Nat.succ_ne_zero]))
        (add norm 0 (by grind only [pow_succ']))
        (add norm 0 (by grind only [Nat.succ_le_succ]))
        (add norm 0 (by grind only [WittVector.map_frobeniusPoly.key₂]))
        (add norm 0 (by grind only [Nat.le_succ]))
        (add norm 0 (by grind only [Nat.factorial_eq_mul_doubleFactorial]))
        (add norm 0 (by grind only [Nat.succ_sub]))
        (add norm 0 (by grind only [Nat.totient_prime_pow_succ]))
        (add norm 0 (by grind only [Polynomial.derivative_pow_succ]))
        (add norm 0 (by grind only [fib_golden_exp']))
        (add norm 0 (by grind only [Nat.mul_one]))
        (add norm 0 (by grind only [WittVector.verschiebung_coeff_succ]))
        (add norm 0 (by grind only [Nat.succ_sub_one]))
        (add norm 0 (by grind only [Nat.succ_pos']))
        (add norm 0 (by grind only [Nat.succ_lt_succ]))
        (add norm 0 (by grind only [gold_pow_sub_gold_pow]))
        (add norm 0 (by grind only [Num.cast_succ]))
        (add norm 0 (by grind only [Nat.mul_comm]))
        (add norm 0 (by grind only [Nat.sub_succ']))

    -- Step 10 & 11: (k+1)^k = (k+1)^((k+1)-1), so (k+1)! < (k+1)^((k+1)-1)
    have h_final : (k + 1) ! < (k + 1) ^ ((k + 1) - 1) := by
      clear * - h_step9
      aesop (config := {
        maxRuleApplications := 1600
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
        (add norm 100 (by rfl))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Nat.succ_mul]))
        (add norm 0 (by grind only [Nat.pow_succ']))
        (add norm 0 (by grind only [Nat.pow_succ]))
        (add norm 0 (by grind only [Nat.mul_succ]))
        (add norm 0 (by grind only [Nat.succ_sub_succ]))
        (add norm 0 (by grind only [Pell.xn_succ]))
        (add norm 0 (by grind only [Nat.succ_pos]))
        (add norm 0 (by grind only [Nat.superFactorial_succ]))
        (add norm 0 (by grind only [Nat.succ_sub_succ_eq_sub]))
        (add norm 0 (by grind only [Nat.succ_eq_add_one]))
        (add norm 0 (by grind only [Nat.succ_le_succ]))
        (add norm 0 (by grind only [pow_succ]))
        (add norm 0 (by grind only [Nat.succ_sub]))
        (add norm 0 (by grind only [WittVector.map_frobeniusPoly.key₂]))
        (add norm 0 (by grind only [Nat.succ_mul_succ]))
        (add norm 0 (by grind only [Nat.succ_ne_zero]))
        (add norm 0 (by grind only [Nat.le_succ]))
        (add norm 0 (by grind only [pow_succ']))
        (add norm 0 (by grind only [Nat.factorial_succ]))
        (add norm 0 (by grind only [Nat.le_of_succ_le_succ]))
        (add norm 0 (by grind only [Nat.succ_pos']))
        (add norm 0 (by grind only [Nat.zero_lt_succ]))
        (add norm 0 (by grind only [Nat.succ_sub_one]))
        (add norm 0 (by grind only [Nat.totient_prime_pow_succ]))
        (add norm 0 (by grind only [Nat.mul_add]))
        (add norm 0 (by grind only [Nat.mul_one]))
        (add norm 0 (by grind only [Nat.succ_add_sub_one]))
        (add norm 0 (by grind only [Nat.mul_comm]))
        (add norm 0 (by grind only [Nat.one_mul]))
        (add norm 0 (by grind only [Nat.sub_succ']))
        (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
        (add unsafe 10% (by grind only [Nat.le_of_lt_succ]))

    exact h_final
