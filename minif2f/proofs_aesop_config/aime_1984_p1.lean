import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem aime_1984_p1 (u : ℕ → ℚ) (h₀ : ∀ n, u (n + 1) = u n + 1)
    (h₁ : (∑ k in Finset.range 98, u k.succ) = 137) :
    (∑ k in Finset.range 49, u (2 * k.succ)) = 93 := by
  let S_even := ∑ k in Finset.range 49, u (2 * k.succ)
  let S_odd := ∑ k in Finset.range 49, u (2 * k + 1)

  have h_split_sum : (∑ k in Finset.range 98, u k.succ) = S_even + S_odd := by
    clear * -
    simp_all only [succ_eq_add_one, S_even, S_odd]
    simp only [Finset.sum_range_succ, mul_add]
    simp_all only [Finset.range_zero, Finset.sum_empty, zero_add, reduceAdd, mul_one, mul_zero, reduceMul]
    ring_nf <;> abel

  have h_pointwise_relation : ∀ k ∈ Finset.range 49, u (2 * k.succ) = u (2 * k + 1) + 1 := by
    clear * - h₀
    simp_all only [Finset.mem_range, succ_eq_add_one]
    any_goals intros; simp_all [mul_add, h₀]

  have h_sum_relation : S_even = S_odd + (49 : ℚ) := by
    clear * - h_pointwise_relation h_split_sum
    simp_all only [succ_eq_add_one, Finset.mem_range, S_even, S_odd]
    simp (config := { decide := true }) only [Finset.sum_range_succ, h_pointwise_relation]
    simp_all only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, mul_one, reduceAdd, reduceMul]
    linarith <;> norm_cast <;> ring

  have h_odd_in_terms_of_even : S_odd = S_even - (49 : ℚ) := by
    clear * - h_sum_relation
    simp_all only [succ_eq_add_one, add_sub_cancel_right, S_even, S_odd]

  have h_substitute_sum : (137 : ℚ) = S_even + (S_even - (49 : ℚ)) := by
    clear * - h₁ h_split_sum h_odd_in_terms_of_even
    simp_all only [succ_eq_add_one, S_even, S_odd]

  have h_arith_1 : (137 : ℚ) = (2 : ℚ) * S_even - (49 : ℚ) := by
    clear * - h_substitute_sum
    simp_all only [succ_eq_add_one, S_even]
    (nlinarith)

  have h_arith_2 : (186 : ℚ) = (2 : ℚ) * S_even := by
    clear * - h_arith_1
    simp_all only [succ_eq_add_one, S_even]
    (nlinarith)

  have h_arith_3 : (93 : ℚ) = S_even := by
    clear * - h_arith_2
    simp_all only [succ_eq_add_one, S_even]
    (nlinarith)

  exact h_arith_3.symm