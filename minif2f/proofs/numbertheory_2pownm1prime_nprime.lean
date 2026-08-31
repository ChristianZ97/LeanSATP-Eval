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
    simp_all only

  have h_pow_pow : (2:ℕ) ^ (a * b) = ((2:ℕ) ^ a) ^ b := by
    clear * -
    (ring)

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
    (gcongr)
    simp only [one_lt_ofNat] at *

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
