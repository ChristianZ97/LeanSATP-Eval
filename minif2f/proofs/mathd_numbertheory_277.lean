import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_numbertheory_277 (m n : ℕ) (h₀ : Nat.gcd m n = 6) (h₁ : Nat.lcm m n = 126) :
    60 ≤ m + n := by
  have h_prod_gcd_lcm : m * n = Nat.gcd m n * Nat.lcm m n := by
    clear * -
    simp_all only [Nat.gcd_mul_lcm]

  have h_prod_val : m * n = 756 := by
    clear * - h_prod_gcd_lcm h₀ h₁
    simp_all only [reduceMul]

  have h_gcd_divides_m : Nat.gcd m n ∣ m := by
    clear * -
    apply Nat.gcd_dvd_left

  have h_gcd_divides_n : Nat.gcd m n ∣ n := by
    clear * -
    rw [Nat.gcd_comm]
    apply Nat.gcd_dvd_left

  have h_six_divides_m : 6 ∣ m := by
    clear * - h₀ h_gcd_divides_m
    simp_all only

  have h_six_divides_n : 6 ∣ n := by
    clear * - h₀ h_gcd_divides_n
    simp_all only

  let a := m / 6
  let b := n / 6

  have h_m_def : m = 6 * a := by
    clear * - h_six_divides_m
    simp_all only [a]
    (omega)

  have h_n_def : n = 6 * b := by
    clear * - h_six_divides_n
    simp_all only [b]
    (omega)

  have h_gcd_ab : Nat.gcd a b = 1 := by
    clear * - h₀ h_m_def h_n_def
    have hab := h₀
    simp_all [Nat.gcd_mul_left, Nat.gcd_comm]

  have h_expand_prod : m * n = 36 * a * b := by
    clear * - h_m_def h_n_def
    rw [h_m_def, h_n_def] <;> (ring)

  have h_ab_val : a * b = 21 := by
    clear * - h_expand_prod h_prod_val
    simp_all only [a, b]
    (linarith)

  have h_sum_def : m + n = 6 * (a + b) := by
    clear * - h_m_def h_n_def
    linear_combination h_m_def + h_n_def

  have h_factor_options : (a = 1 ∧ b = 21) ∨ (a = 21 ∧ b = 1) ∨ (a = 3 ∧ b = 7) ∨ (a = 7 ∧ b = 3) := by
    clear * - h_ab_val h_gcd_ab
    revert h_ab_val
    rw [Nat.gcd_eq_iff] at h_gcd_ab
    cases' a with a <;> cases' b with b <;> aesop
    have h_a : a < 21 := by nlinarith
    interval_cases a <;> repeat' omega

  have h_case_1_sum : (a = 1 ∧ b = 21) → m + n = 132 := by
    clear * - h_sum_def
    intro a_1
    simp_all only [reduceAdd, reduceMul, a, b]

  have h_case_2_sum : (a = 3 ∧ b = 7) → m + n = 60 := by
    clear * - h_sum_def
    intro a_1
    simp_all only [reduceAdd, reduceMul, a, b]

  have h_symm_case_1 : (a = 21 ∧ b = 1) → m + n = 132 := by
    clear * - h_sum_def
    intro a_1
    simp_all only [reduceAdd, reduceMul, a, b]

  have h_symm_case_2 : (a = 7 ∧ b = 3) → m + n = 60 := by
    clear * - h_sum_def
    intro a_1
    simp_all only [reduceAdd, reduceMul, a, b]

  have h_possible_sums : m + n = 132 ∨ m + n = 60 := by
    clear * - h_factor_options h_case_1_sum h_symm_case_1 h_case_2_sum h_symm_case_2
    simp_all only [and_imp, a, b]
    (grind only [FiniteInter.finiteInterClosure_insert])

  have h_final_leq : 60 ≤ m + n := by
    clear * - h_possible_sums
    (omega)

  exact h_final_leq
