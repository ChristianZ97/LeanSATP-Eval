import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  have h_n_gt_1 : (1:ℕ) < n := by
    clear * - h₁
    by_contra h₂
    interval_cases n <;> norm_cast at h₁ h₂ ⊢

  by_contra hn

  have h_composite : ∃ (a b : ℕ), n = a * b ∧ (1:ℕ) < a ∧ a < n := by
    clear * - hn h_n_gt_1
    rw [Nat.prime_def_lt'] at hn
    cases' n with pn
    · try cases h_n_gt_1
    · cases pn <;> aesop

  obtain ⟨a, b, h_n_eq_ab, h_a_gt_1, h_a_lt_n⟩ := h_composite

  have h_exp_subst : (2:ℕ) ^ n - 1 = (2:ℕ) ^ (a * b) - 1 := by
    clear * - h_n_eq_ab
    aesop (config := {
      maxRuleApplications := 400
      maxRuleApplicationDepth := 10
      maxNormIterations := 30
      maxGoals := 1024
      enableUnfold := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 100 (by zify))
      (add norm 100 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by decide))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by ring_nf))
      (add safe 0 (by simp_all))
      (add norm 0 (by grind only [nat_sub_dvd_pow_sub_pow]))
      (add norm 0 (by grind only [pow_succ]))
      (add norm 0 (by grind only [tsub_add_cancel_of_le]))
      (add norm 0 (by grind only [pow_succ']))
      (add norm 0 (by grind only [Nat.add_sub_assoc]))
      (add norm 0 (by grind only [mul_tsub]))
      (add norm 0 (by grind only [Nat.sub_add_comm]))
      (add norm 0 (by grind only [pow_mul']))
      (add norm 0 (by grind only [Nat.add_sub_of_le]))
      (add norm 0 (by grind only [gold_pow_sub_gold_pow]))
      (add norm 0 (by grind only [Nat.add_sub_cancel']))
      (add norm 0 (by grind only [add_tsub_cancel_of_le]))
      (add unsafe 10% (by push_cast [pow_add] at *))
      (add unsafe 90% (by simp_rw [Nat.bp_helper]))
      (add unsafe 10% (by push_cast [pow_mul] at *))
      (add unsafe 10% (by push_cast [Nat.sq_sub_sq] at *))
      (add unsafe 10% (by push_cast [Nat.sub_add_cancel] at *))
      (add unsafe 10% (by push_cast [Nat.pow_succ'] at *))
      (add unsafe 90% (by simp_rw [PerfectClosure.mk_pow]))
      (add unsafe 10% (by rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add unsafe 10% (by rw [neg_one_sq]))
      (add unsafe 10% (by rw [jacobiSym.quadratic_reciprocity]))
      (add unsafe 10% (by push_cast [mul_pow] at *))
      (add unsafe 10% (by push_cast [Nat.even_pow'] at *))
      (add unsafe 90% (by simp_rw [IsNilpotent.pow_succ]))
      (add unsafe 10% (by rw [LucasLehmer.ω_pow_eq_neg_one]))
      (add unsafe 90% (by simp_rw [ppow_mul]))
      (add unsafe 10% (by rw [LucasLehmer.ω_pow_eq_one]))
      (add unsafe 10% (by push_cast [Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one] at *))
      (add unsafe 10% (by push_cast [ZMod.neg_one_pow_div_two_of_three_mod_four] at *))
      (add unsafe 10% (by rw [qrSign.sq_eq_one]))
      (add unsafe 90% (by simp_rw [npow_mul]))

  have h_pow_pow : (2:ℕ) ^ (a * b) = ((2:ℕ) ^ a) ^ b := by
    clear * -
    aesop (config := {
      maxRuleApplications := 400
      maxRuleApplicationDepth := 10
      maxNormIterations := 30
      maxGoals := 64
      enableUnfold := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 100 (by zify))
      (add norm 100 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by decide))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by ring_nf))
      (add safe 0 (by simp_all))
      (add norm 0 (by simp [Nat.pow_succ] at *))
      (add norm 0 (by grind only [nat_sub_dvd_pow_sub_pow]))
      (add norm 0 (by grind only [pow_succ]))
      (add norm 0 (by simp [Nat.mul_assoc] at *))
      (add unsafe 10% (by rw [pow_mul]))
      (add unsafe 10% (by rw [pow_mul']))
      (add unsafe 10% (by rw [pow_add]))
      (add unsafe 10% (by rw [Nat.bp_helper]))
      (add unsafe 10% (by rw [Nat.pow_succ']))
      (add unsafe 10% (by push_cast [Nat.even_pow'] at *))
      (add unsafe 10% (by rw [jacobiSym.quadratic_reciprocity]))
      (add unsafe 10% (by rw [Nat.AB_id_helper]))
      (add unsafe 10% (by rw [Nat.sq_sub_sq]))
      (add unsafe 10% (by push_cast [mul_pow] at *))
      (add unsafe 10% (by rw [Nat.superFactorial_four_mul]))
      (add unsafe 10% (by rw [npow_mul]))
      (add unsafe 90% (by simp_rw [Nat.mul_pow]))
      (add unsafe 10% (by rw [Nat.sq_add_sq_mul]))
      (add unsafe 10% (by rw [ppow_mul]))
      (add unsafe 10% (by rw [PerfectClosure.mk_pow]))
      (add unsafe 10% (by rw [Nat.mul_div_right]))
      (add unsafe 10% (by rw [Nat.mul_div_left]))
      (add unsafe 10% (by rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add unsafe 10% (by rw [ZMod.χ₄_eq_neg_one_pow]))
      (add unsafe 90% (by norm_num [Surreal.nsmul_pow_two_powHalf'] at *))
      (add unsafe 10% (by rw [pow_succ']))
      (add unsafe 10% (by rw [Nat.mul_div_cancel_left]))
      (add unsafe 10% (by push_cast [ZMod.neg_one_pow_div_two_of_three_mod_four] at *))
      (add unsafe 10% (by rw [ArithmeticFunction.vonMangoldt_apply_pow]))
      (add unsafe 10% (by rw [LucasLehmer.ω_pow_eq_neg_one]))
      (add unsafe 10% (by rw [LucasLehmer.ω_pow_eq_one]))
      (add unsafe 10% (by rw [Nat.mul_div_cancel]))

  have h_dvd_factor : ((2:ℕ) ^ a - 1) ∣ ((2:ℕ) ^ n - 1) := by
    clear * - h_exp_subst h_pow_pow
    rw [h_exp_subst, h_pow_pow]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ a) b

  have h_divisor_gt_1 : (1:ℕ) < ((2:ℕ) ^ a - 1) := by
    clear * - h_a_gt_1
    have h_two_pos : 0 < 2
    · norm_num
    · induction h_a_gt_1 <;> simp [*, pow_succ] at * <;> omega

  have h_pow_mono : ((2:ℕ) ^ a) < ((2:ℕ) ^ n) := by
    clear * - h_a_lt_n
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 30
      maxGoals := 256
      useSimpAll := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 0 (by gcongr))
      (add norm 100 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 1 (by zify))
      (add safe 1 (by ring_nf))
      (add safe 0 (by simp_all))
      (add norm 100 (by rw [← Nat.lt_two_pow]))
      (add norm 0 (by rw [← Nat.mul_lt_mul_pow_succ]))
      (add norm 100 (by rw [← Nat.pow_lt_pow_left]))
      (add norm 100 (by simp_all [Nat.lt_pow_self]))
      (add norm 0 (by rw [← Nat.mul_lt_mul_right]))
      (add norm 100 (by simp_all only [Nat.four_pow_lt_mul_centralBinom]))
      (add norm 0 (by rw [← Nat.mul_lt_mul_of_pos_left]))
      (add norm 100 (by rw [← Nat.pow_lt_pow_iff_right]))
      (add norm 100 (by rw [← Nat.mul_lt_mul_left]))
      (add norm 100 (by rw [← Nat.lt_pow_succ_log_self]))
      (add norm 100 (by rw [← Nat.mul_pos]))
      (add norm 0 (by grind only [gold_lt_two]))
      (add norm 100 (by rw [← Nat.pow_lt_pow_right]))
      (add norm 0 (by rw [← Nat.mul_lt_mul_of_lt_of_le']))
      (add norm 0 (by rw [← Nat.mul_lt_mul_of_le_of_lt]))
      (add norm 0 (by rw [← Nat.ofDigits_lt_base_pow_length]))
      (add norm 0 (by rw [← Nat.mul_lt_mul_of_pos_right]))
      (add norm 0 (by grind only [Nat.lt_of_succ_le]))
      (add safe 0 (by simp_rw [pow_lt_pow_right]))
      (add unsafe 90% (by field_simp [pow_lt_pow_right₀] at *))
      (add unsafe 90% (by field_simp [pow_lt_pow_succ] at *))
      (add unsafe 10% (by simp_all only [Pell.eq_pow_of_pell_lem]))
      (add unsafe 90% (by field_simp [pow_lt_pow_left] at *))
      (add unsafe 10% (by simp_all only [Nat.sub_lt]))
      (add unsafe 90% (by field_simp [pow_lt_pow_iff_right] at *))
      (add unsafe 90% (by field_simp [lt_of_pow_lt_pow_left] at *))
      (add unsafe 90% (by field_simp [Monotone.seq_pos_lt_seq_of_le_of_lt] at *))
      (add unsafe 90% (by field_simp [mul_lt_mul] at *))
      (add unsafe 90% (by field_simp [Real.pi_lt_sqrtTwoAddSeries] at *))
      (add unsafe 90% (by field_simp [lt_self_pow] at *))
      (add unsafe 90% (by field_simp [pow_lt_pow_right_of_lt_one] at *))
      (add unsafe 90% (by field_simp [Int.lt_of_sum_four_squares_eq_mul] at *))

  have h_divisor_lt_self : ((2:ℕ) ^ a - 1) < ((2:ℕ) ^ n - 1) := by
    clear * - h_pow_mono
    have h_base : 1 < 2 := by norm_num
    apply Nat.pred_lt_pred
    · simp
    · simpa

  have h_mersenne_not_prime : ¬ Nat.Prime ((2:ℕ) ^ n - 1) := by
    clear * - h_dvd_factor h_divisor_gt_1 h_divisor_lt_self
    cases' h_dvd_factor with k h
    rw [h, Nat.prime_mul_iff]
    any_goals aesop

  exact h_mersenne_not_prime h₁
