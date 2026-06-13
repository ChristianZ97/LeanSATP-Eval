import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_495 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a % 10 = 2) (h₂ : b % 10 = 4)
    (h₃ : Nat.gcd a b = 6) : 108 ≤ Nat.lcm a b := by
  have h_lcm_prod : Nat.lcm a b * Nat.gcd a b = a * b := by
    clear * -
    nth_rw 1 [← Nat.gcd_mul_lcm a b]
    rw [mul_comm]

  have h_lcm_eq : Nat.lcm a b = (a * b) / 6 := by
    clear * - h_lcm_prod h₃
    simp_all only
    (omega)

  have h_6_dvd_a : 6 ∣ a := by
    clear * - h₃
    have := h₃ ▸ Nat.gcd_dvd_left a b
    simp_all only

  have h_6_dvd_b : 6 ∣ b := by
    clear * - h₃
    have : a.gcd b = 6 := h₃
    simp_all only
    have : 6 = a.gcd b
    · simp_all only
    · simp_all only
      apply Nat.gcd_dvd_right

  have h_a_mod_6 : a % 6 = 0 := by
    clear * - h_6_dvd_a
    (omega)

  have h_b_mod_6 : b % 6 = 0 := by
    clear * - h_6_dvd_b
    (omega)

  have h_a_ge_12 : 12 ≤ a := by
    clear * - h₁ h_a_mod_6
    (omega)

  have h_b_ge_24 : 24 ≤ b := by
    clear * - h₂ h_b_mod_6
    (omega)

  have h_a_cases : a = 12 ∨ 42 ≤ a := by
    clear * - h₁ h_a_mod_6
    (omega)

  have h_b_cases : b = 24 ∨ 54 ≤ b := by
    clear * - h₂ h_b_mod_6
    (omega)

  have h_gcd_12_24 : Nat.gcd 12 24 = 12 := by
    clear * -
    simp_all only [reduceGcd]

  have h_not_12_24 : ¬ (a = 12 ∧ b = 24) := by
    clear * - h_gcd_12_24 h₃
    simp_all only [reduceGcd, not_and]
    intro a_1
    subst a_1
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only [reduceGcd, reduceEqDiff]

  have h_if_a_12_then_b_54 : a = 12 → 54 ≤ b := by
    clear * - h_b_cases h_not_12_24
    intro a_1
    subst a_1
    simp_all only [true_and, false_or]

  have h_case_1 : a = 12 → 108 ≤ Nat.lcm a b := by
    clear * - h_if_a_12_then_b_54 h_lcm_eq
    intro a_1
    subst a_1
    simp_all only [forall_const]
    (omega)

  have h_case_2 : 42 ≤ a → 108 ≤ Nat.lcm a b := by
    clear * - h_b_ge_24 h_lcm_eq
    simp_all only
    exact fun h_42_le_a ↦ by
      rw [Nat.le_div_iff_mul_le (by norm_num), mul_comm]
      nlinarith

  have h_final : 108 ≤ Nat.lcm a b := by
    clear * - h_a_cases h_case_1 h_case_2
    simp_all only
    cases h_a_cases with
    | inl h =>
      subst h
      simp_all only [forall_const, reduceLeDiff, implies_true]
    | inr h_1 => simp_all only [forall_const]

  exact h_final
