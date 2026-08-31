import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12a_2003_p5 (A M C : ℕ) (h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
    (h₁ : Nat.ofDigits 10 [0, 1, C, M, A] + Nat.ofDigits 10 [2, 1, C, M, A] = 123422) :
    A + M + C = 14 := by
  have h₁_exp : Nat.ofDigits 10 [0, 1, C, M, A] = 0 + 1 * 10 + C * 100 + M * 1000 + A * 10000 := by
    clear * - h₁
    simp_all only [one_mul, zero_add]
    (grind only [Nat.ofDigits_cons])

  have h₂_exp : Nat.ofDigits 10 [2, 1, C, M, A] = 2 + 1 * 10 + C * 100 + M * 1000 + A * 10000 := by
    clear * - h₁
    simp_all only [one_mul, reduceAdd]
    (grind only [Nat.ofDigits_cons])

  have h₃_sum : (0 + 10 + 100 * C + 1000 * M + 10000 * A) + (2 + 10 + 100 * C + 1000 * M + 10000 * A) = 123422 := by
    clear * - h₁ h₁_exp h₂_exp
    simp_all only [one_mul, zero_add, reduceAdd]
    (linarith)

  have h₄_simp : 22 + 200 * C + 2000 * M + 20000 * A = 123422 := by
    clear * - h₃_sum
    simp_all only [zero_add, reduceAdd]
    (linarith)

  have h₅_sub : 200 * C + 2000 * M + 20000 * A = 123400 := by
    clear * - h₄_simp
    (linarith)

  have h₆_fact : 200 * (C + 10 * M + 100 * A) = 123400 := by
    clear * - h₅_sub
    (linarith)

  have h₇_norm : C + 10 * M + 100 * A = 617 := by
    clear * - h₆_fact
    (linarith)

  have h₈_A_le : 100 * A ≤ 617 := by
    clear * - h₇_norm h₀
    (linarith)

  have h₉_A_ge : 100 * A ≥ 518 := by
    clear * - h₇_norm h₀
    simp only [ge_iff_le] at *
    (linarith)

  have h₁₀_A_val : A = 6 := by
    clear * - h₈_A_le h₉_A_ge
    simp only [ge_iff_le] at *
    (linarith)

  have h₁₁_sub_A : C + 10 * M + 600 = 617 := by
    clear * - h₇_norm h₁₀_A_val
    subst h₁₀_A_val
    simp_all only [reduceMul, reduceEqDiff, reduceAdd]

  have h₁₂_MC : C + 10 * M = 17 := by
    clear * - h₁₁_sub_A
    simp_all only [reduceEqDiff]

  have h₁₃_M_le : 10 * M ≤ 17 := by
    clear * - h₁₂_MC h₀
    (linarith)

  have h₁₄_M_ge : 10 * M ≥ 8 := by
    clear * - h₁₂_MC h₀
    simp only [ge_iff_le] at *
    (linarith)

  have h₁₅_M_val : M = 1 := by
    clear * - h₁₃_M_le h₁₄_M_ge
    simp only [ge_iff_le] at *
    (linarith)

  have h₁₆_C_val : C = 7 := by
    clear * - h₁₂_MC h₁₅_M_val
    simp_all only [mul_one, reduceEqDiff]

  have h₁₇_final : A + M + C = 14 := by
    clear * - h₁₀_A_val h₁₅_M_val h₁₆_C_val
    subst h₁₀_A_val h₁₅_M_val h₁₆_C_val
    simp_all only [reduceAdd]

  exact h₁₇_final
