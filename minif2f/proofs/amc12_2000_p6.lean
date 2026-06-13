import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) (h₁ : 4 ≤ p ∧ p ≤ 18)
    (h₂ : 4 ≤ q ∧ q ≤ 18) : ↑p * ↑q - (↑p + ↑q) ≠ (194 : ℕ) := by
  intro h_eq
  have h_step1 : p * q - (p + q) = 194 := by
    rw [show (↑p : ℕ) = p by simp, show (↑q : ℕ) = q by simp] at h_eq
    exact h_eq

  have h_step2 : p * q - p - q + 1 = 195 := by
    omega

  have h_step3 : (p - 1) * (q - 1) = 195 := by
    have h_temp : p * q - p - q + 1 = (p - 1) * (q - 1) := by
      cases p <;> cases q <;> norm_num at h_step2 ⊢ <;> ring_nf at h_step2 ⊢ <;> omega

    rw [h_temp] at h_step2
    exact h_step2

  have h_step4 : 3 ≤ p - 1 ∧ p - 1 ≤ 17 := by
    have h_p_ge : 4 ≤ p := h₁.1
    have h_p_le : p ≤ 18 := h₁.2
    constructor
    · omega
    · omega

  have h_step5 : p - 1 = 3 ∨ p - 1 = 5 ∨ p - 1 = 13 ∨ p - 1 = 15 := by
    have h_factors : 195 = 3 * 65 ∧ 195 = 5 * 39 ∧ 195 = 13 * 15 := by norm_num
    clear * - h_step3 h_step4
    simp_all only [tsub_le_iff_right, reduceAdd, pred_eq_succ_iff]
    cases' h_step4 with h_left h_right
    interval_cases p <;> omega

  have h_step6 : False := by
    rcases h_step5 with (h | h | h | h)
    · -- Case 1: p - 1 = 3 => p = 4
      have h_p_val : p = 4 := by omega
      have h_not_prime : ¬ Nat.Prime 4 := by decide
      have h_is_prime : Nat.Prime p := h₀.1
      rw [h_p_val] at h_is_prime
      exact h_not_prime h_is_prime

    · -- Case 2: p - 1 = 5 => p = 6
      have h_p_val : p = 6 := by omega
      have h_not_prime : ¬ Nat.Prime 6 := by decide
      have h_is_prime : Nat.Prime p := h₀.1
      rw [h_p_val] at h_is_prime
      exact h_not_prime h_is_prime

    · -- Case 3: p - 1 = 13 => p = 14
      have h_p_val : p = 14 := by omega
      have h_not_prime : ¬ Nat.Prime 14 := by decide
      have h_is_prime : Nat.Prime p := h₀.1
      rw [h_p_val] at h_is_prime
      exact h_not_prime h_is_prime

    · -- Case 4: p - 1 = 15 => p = 16
      have h_p_val : p = 16 := by omega
      have h_not_prime : ¬ Nat.Prime 16 := by decide
      have h_is_prime : Nat.Prime p := h₀.1
      rw [h_p_val] at h_is_prime
      exact h_not_prime h_is_prime

  exfalso
  exact h_step6
