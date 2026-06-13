import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_711 (m n : ℕ) (h₀ : 0 < m ∧ 0 < n) (h₁ : Nat.gcd m n = 8)
    (h₂ : Nat.lcm m n = 112) : 72 ≤ m + n := by
  have h_prod_id : m * n = Nat.gcd m n * Nat.lcm m n := by
    clear * -
    exact Eq.symm (Nat.gcd_mul_lcm m n)

  have h_prod_subst : m * n = 8 * 112 := by
    clear * - h_prod_id h₁ h₂
    simp_all only [reduceMul]

  have h_prod_val : m * n = 896 := by
    clear * - h_prod_subst
    simp_all only [reduceMul]

  have h_m_div_8 : 8 ∣ m := by
    clear * - h₁
    have : m.gcd n = 8 := h₁
    simp_all only
    have gcd_dvd_left : m.gcd n ∣ m
    · simp_all only
      rewrite [← this]
      simp_all only
      apply this ▸ Nat.gcd_dvd_left m n
    · simp_all only

  have h_n_div_8 : 8 ∣ n := by
    clear * - h₁
    have : m.gcd n = 8
    · simp_all only
    · simp_all only
      have gcd_dvd_right := Nat.gcd_dvd_right m n
      simp_all only

  obtain ⟨a, ha⟩ : ∃ a, m = 8 * a := by
    clear * - h_m_div_8
    exact h_m_div_8

  obtain ⟨b, hb⟩ : ∃ b, n = 8 * b := by
    clear * - h_n_div_8
    exact h_n_div_8

  have h_sub_prod : (8 * a) * (8 * b) = 896 := by
    clear * - ha hb h_prod_val
    subst ha hb
    simp_all only

  have h_expand : 64 * a * b = 896 := by
    clear * - h_sub_prod
    (nlinarith)

  have h_ab_eq : a * b = 14 := by
    clear * - h_expand
    (nlinarith)

  have h_ab_coprime : Nat.gcd a b = 1 := by
    clear * - h₁ ha hb
    simp_all only
    have h := h₁
    simp_all only
    simp [Nat.gcd_mul_left, Nat.gcd_comm] at h <;> aesop

  have h_final_lower_bound : 72 ≤ m + n := by
    clear * - h_ab_eq h_ab_coprime ha hb
    simp_all only
    by_contra hyp
    simp_all only [not_le]
    all_goals
      have : a < 9 := by nlinarith
      have : b < 9 := by nlinarith
      interval_cases a <;> interval_cases b <;> omega

  exact h_final_lower_bound
