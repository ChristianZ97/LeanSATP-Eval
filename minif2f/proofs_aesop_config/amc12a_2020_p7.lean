import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12a_2020_p7 (a : ℕ → ℕ) (h₀ : a 0 ^ 3 = 1) (h₁ : a 1 ^ 3 = 8) (h₂ : a 2 ^ 3 = 27)
    (h₃ : a 3 ^ 3 = 64) (h₄ : a 4 ^ 3 = 125) (h₅ : a 5 ^ 3 = 216) (h₆ : a 6 ^ 3 = 343) :
    ↑(6 * ∑ k in Finset.range 7, (a k)^2) - ↑(2 * ∑ k in Finset.range 6, (a k)^2) = (658 : ℤ) := by
  have step_1 : a 0 = 1 := by
    clear * - h₀
    any_goals
    have h₁ := sq_nonneg (a 0 ^ 2)
    nlinarith

  have step_2 : a 1 = 2 := by
    clear * - h₁
    nlinarith [sq_nonneg (a 1 ^ 2)]

  have step_3 : a 2 = 3 := by
    clear * - h₂
    nlinarith [sq_nonneg (a 2), sq_nonneg (a 2 ^ 2)]

  have step_4 : a 3 = 4 := by
    clear * - h₃
    repeat' nlinarith [sq_nonneg (a 3), sq_nonneg (a 3 ^ 2)]

  have step_5 : a 4 = 5 := by
    clear * - h₄
    nlinarith [sq_nonneg (a 4), sq_nonneg (a 4 ^ 2)]

  have step_6 : a 5 = 6 := by
    clear * - h₅
    nlinarith [sq (a 5), sq_nonneg (a 5)]

  have step_7 : a 6 = 7 := by
    clear * - h₆
    nlinarith [sq_nonneg (a 6 ^ 2), sq_nonneg (a 6)]

  have step_8 : ∑ k in Finset.range 7, (a k)^2 = 1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2 := by
    clear * - step_1 step_2 step_3 step_4 step_5 step_6 step_7
    simp_all only [one_pow, reducePow, reduceAdd]
    norm_num [Finset.sum, Finset.range_succ, *]

  have step_9 : (1 : ℕ)^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2 = 140 := by
    clear * -
    simp_all only [one_pow, reducePow, reduceAdd]

  have step_10 : ∑ k in Finset.range 7, (a k)^2 = 140 := by
    clear * - step_8 step_9
    simp_all only [one_pow, reducePow, reduceAdd]

  have step_11 : ∑ k in Finset.range 6, (a k)^2 = 1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 := by
    clear * - step_1 step_2 step_3 step_4 step_5 step_6
    simp_all only [one_pow, reducePow, reduceAdd]
    simp [Finset.sum_range_succ, *] <;> norm_cast

  have step_12 : (1 : ℕ)^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 = 91 := by
    clear * -
    simp_all only [one_pow, reducePow, reduceAdd]

  have step_13 : ∑ k in Finset.range 6, (a k)^2 = 91 := by
    clear * - step_11 step_12
    simp_all only [one_pow, reducePow, reduceAdd]

  have step_14_part1 : (6 : ℤ) * (140 : ℤ) = (840 : ℤ) := by
    clear * -
    simp_all only [Int.reduceMul]

  have step_14_part2 : (2 : ℤ) * (91 : ℤ) = (182 : ℤ) := by
    clear * -
    simp_all only [Int.reduceMul]

  have step_14_conn1 : ↑(6 * ∑ k in Finset.range 7, (a k)^2) = (840 : ℤ) := by
    clear * - step_10 step_14_part1
    simp_all only [Int.reduceMul, reduceMul, Nat.cast_ofNat]

  have step_14_conn2 : ↑(2 * ∑ k in Finset.range 6, (a k)^2) = (182 : ℤ) := by
    clear * - step_13 step_14_part2
    simp_all only [Int.reduceMul, reduceMul, Nat.cast_ofNat]

  have step_15 : (840 : ℤ) - (182 : ℤ) = (658 : ℤ) := by
    clear * -
    simp_all only [Int.reduceSub]

  have h_conclusion : ↑(6 * ∑ k in Finset.range 7, (a k)^2) - ↑(2 * ∑ k in Finset.range 6, (a k)^2) = (658 : ℤ) := by
    clear * - step_14_conn1 step_14_conn2 step_15
    simp_all only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_pow, Int.reduceSub]

  exact h_conclusion