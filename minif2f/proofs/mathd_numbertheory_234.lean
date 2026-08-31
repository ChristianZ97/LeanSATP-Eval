import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by
  let n := 10 * a + b

  have h_step2 : n ^ 3 = 912673 := by
    clear * - h₁
    simp_all only [n]

  have h_step3 : 90 ^ 3 = 729000 := by
    clear * -
    simp_all only [reducePow]

  have h_step4 : 729000 < 912673 := by
    clear * -
    simp_all only [reduceLT]

  have h_step5 : 90 ^ 3 < n ^ 3 := by
    clear * - h_step2 h_step3 h_step4
    simp only [reducePow, reduceLT, n] at *
    (nlinarith)

  have h_step6 : 90 < n := by
    clear * - h_step5
    any_goals nlinarith [sq_nonneg (n ^ 2)]

  have h_step7 : 100 ^ 3 = 1000000 := by
    clear * -
    simp_all only [reducePow]

  have h_step8 : 912673 < 1000000 := by
    clear * -
    simp_all only [reduceLT]

  have h_step9 : n ^ 3 < 100 ^ 3 := by
    clear * - h_step2 h_step7 h_step8
    simp only [reducePow, reduceLT, n] at *
    (nlinarith)

  have h_step10 : n < 100 := by
    clear * - h_step9
    nlinarith [pow_nonneg (sq_nonneg n) 2, pow_nonneg (sq_nonneg n) 3]

  have h_a_eq_9 : a = 9 := by
    clear * - h₀ h_step6 h_step10
    simp_all only [n]
    (linarith)

  have h_b_eq_7 : b = 7 := by
    clear * - h₀ h_a_eq_9 h₁
    (bound )
    simp only [reduceMul, one_le_ofNat, le_refl] at *
    (ring_nf at *)
    (nlinarith)

  have h_result : a + b = 16 := by
    clear * - h_a_eq_9 h_b_eq_7
    simp_all only [reduceAdd]

  exact h_result
