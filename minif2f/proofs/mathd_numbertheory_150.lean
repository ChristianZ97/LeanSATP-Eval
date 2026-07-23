import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_numbertheory_150 (n : ℕ) (h₀ : ¬Nat.Prime (7 + 30 * n)) : 6 ≤ n := by
  have h_step1 : n < 6 ↔ n ≤ 5 := by
    clear * -
    (omega)

  have h_step2 : (7 + 30 * 0 : ℕ) = 7 := by
    clear * -
    (linarith)

  have h_step3 : Nat.Prime 7 := by
    clear * -
    (bound )

  have h_step3b : Nat.Prime (7 + 30 * 0) := by
    clear * - h_step2 h_step3
    simp_all only [mul_zero, add_zero]

  have h_step4 : (7 + 30 * 1 : ℕ) = 37 := by
    clear * -
    simp_all only [mul_one, reduceAdd]

  have h_step5 : Nat.Prime 37 := by
    clear * -
    (bound )

  have h_step5b : Nat.Prime (7 + 30 * 1) := by
    clear * - h_step4 h_step5
    simp_all only [mul_one, reduceAdd]

  have h_step6 : (7 + 30 * 2 : ℕ) = 67 := by
    clear * -
    simp_all only [reduceMul, reduceAdd]

  have h_step7 : Nat.Prime 67 := by
    clear * -
    (bound )

  have h_step7b : Nat.Prime (7 + 30 * 2) := by
    clear * - h_step6 h_step7
    simp_all only [reduceMul, reduceAdd]

  have h_step8 : (7 + 30 * 3 : ℕ) = 97 := by
    clear * -
    simp_all only [reduceMul, reduceAdd]

  have h_step9 : Nat.Prime 97 := by
    clear * -
    (bound )

  have h_step9b : Nat.Prime (7 + 30 * 3) := by
    clear * - h_step8 h_step9
    simp_all only [reduceMul, reduceAdd]

  have h_step10 : (7 + 30 * 4 : ℕ) = 127 := by
    clear * -
    simp_all only [reduceMul, reduceAdd]

  have h_step11 : Nat.Prime 127 := by
    clear * -
    (bound )

  have h_step11b : Nat.Prime (7 + 30 * 4) := by
    clear * - h_step10 h_step11
    simp_all only [reduceMul, reduceAdd]

  have h_step12 : (7 + 30 * 5 : ℕ) = 157 := by
    clear * -
    simp_all only [reduceMul, reduceAdd]

  have h_step13 : Nat.Prime 157 := by
    clear * -
    (bound )

  have h_step13b : Nat.Prime (7 + 30 * 5) := by
    clear * - h_step12 h_step13
    simp_all only [reduceMul, reduceAdd]

  have h_step14 : ∀ k, k < 6 → Nat.Prime (7 + 30 * k) := by
    clear * - h_step3b h_step5b h_step7b h_step9b h_step11b h_step13b
    simp only [mul_zero, add_zero, mul_one, reduceAdd, reduceMul] at *
    (grind only [Nat.succ_lt_succ])

  have h_step15 : n < 6 → Nat.Prime (7 + 30 * n) := by
    clear * - h_step14
    (bound )

  have h_step16 : ¬(n < 6) := by
    clear * - h_step15 h₀
    intro lt_6
    classical
    have := h_step15 lt_6
    norm_num at *
    tauto

  have h_step17 : 6 ≤ n := by
    clear * - h_step16
    simp only [not_lt] at *
    (linarith)

  exact h_step17
