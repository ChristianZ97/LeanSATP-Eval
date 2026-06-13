import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12a_2003_p5 (A M C : ℕ) (h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
    (h₁ : Nat.ofDigits 10 [0, 1, C, M, A] + Nat.ofDigits 10 [2, 1, C, M, A] = 123422) :
    A + M + C = 14 := by
  have h_val1 : Nat.ofDigits 10 [0, 1, C, M, A] = 10 + 100 * C + 1000 * M + 10000 * A := by
    clear * -
    dsimp [ofDigits]
    simp_all only [zero_add]
    linear_combination 10 * C + 100 * M + 1000 * A + 10

  have h_val2 : Nat.ofDigits 10 [2, 1, C, M, A] = 12 + 100 * C + 1000 * M + 10000 * A := by
    clear * -
    dsimp [ofDigits]
    first
    | linarith
    | abel

  have h_sum_expanded : (10 + 100 * C + 1000 * M + 10000 * A) + (12 + 100 * C + 1000 * M + 10000 * A) = 123422 := by
    clear * - h₁ h_val1 h_val2
    simp_all only

  have h_sum_combined : 22 + 100 * C + 100 * C + 1000 * M + 1000 * M + 10000 * A + 10000 * A = 123422 := by
    clear * - h_sum_expanded
    (nlinarith)

  have h_c_terms : 22 + 200 * C + 1000 * M + 1000 * M + 10000 * A + 10000 * A = 123422 := by
    clear * - h_sum_combined
    (nlinarith)

  have h_m_terms : 22 + 200 * C + 2000 * M + 10000 * A + 10000 * A = 123422 := by
    clear * - h_c_terms
    (nlinarith)

  have h_a_terms : 22 + 200 * C + 2000 * M + 20000 * A = 123422 := by
    clear * - h_m_terms
    (nlinarith)

  have h_move_const : 200 * C + 2000 * M + 20000 * A = 123400 := by
    clear * - h_a_terms
    (nlinarith)

  have h_factor_out : 200 * (C + 10 * M + 100 * A) = 123400 := by
    clear * - h_move_const
    (nlinarith)

  have h_after_divide : C + 10 * M + 100 * A = 617 := by
    clear * - h_factor_out
    (nlinarith)

  have h_A_eq : A = 6 := by
    clear * - h_after_divide h₀
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    (nlinarith)

  have h_substitute_A : C + 10 * M + 100 * 6 = 617 := by
    clear * - h_after_divide h_A_eq
    subst h_A_eq
    simp_all only [reduceMul, reduceEqDiff, reduceAdd]

  have h_after_A : C + 10 * M = 17 := by
    clear * - h_substitute_A
    simp_all only [reduceMul, reduceEqDiff]

  have h_M_eq : M = 1 := by
    clear * - h_after_A h₀
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    (nlinarith)

  have h_substitute_M : C + 10 * 1 = 17 := by
    clear * - h_after_A h_M_eq
    subst h_M_eq
    simp_all only [mul_one, reduceEqDiff, reduceAdd]

  have h_C_eq : C = 7 := by
    clear * - h_substitute_M
    simp_all only [mul_one, reduceEqDiff]

  have h_final : A + M + C = 14 := by
    clear * - h_A_eq h_M_eq h_C_eq
    subst h_M_eq h_C_eq h_A_eq
    simp_all only [reduceAdd]

  exact h_final