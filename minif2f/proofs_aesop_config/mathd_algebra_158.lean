import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k in Finset.range 8, (2 * k + 1)) - ↑(∑ k in Finset.range 5, (a + 2 * k)) = (4 : ℤ)) :
    a = 8 := by
  have h_sum_k_8 : ∑ k in Finset.range 8, k = 28 := by
    clear * -
    rfl

  have h_sum_one_8 : ∑ k in Finset.range 8, (1 : ℕ) = 8 := by
    clear * -
    simp_all only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

  have h_split_sum1 : ∑ k in Finset.range 8, (2 * k + 1) = 2 * ∑ k in Finset.range 8, k + ∑ k in Finset.range 8, (1 : ℕ) := by
    clear * -
    simp_all only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    rfl

  have h_val_sum1 : ∑ k in Finset.range 8, (2 * k + 1) = 64 := by
    clear * - h_sum_k_8 h_sum_one_8 h_split_sum1
    simp_all only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, reduceMul, reduceAdd]

  have h_sum_k_5 : ∑ k in Finset.range 5, k = 10 := by
    clear * -
    rfl

  have h_sum_a_5 : ∑ k in Finset.range 5, a = 5 * a := by
    clear * -
    simp_all only [Finset.sum_const, Finset.card_range, smul_eq_mul]

  have h_split_sum2 : ∑ k in Finset.range 5, (a + 2 * k) = ∑ k in Finset.range 5, a + 2 * ∑ k in Finset.range 5, k := by
    clear * -
    simp_all only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp_all only [zero_add, mul_one, mul_zero, add_zero]
    simp [Finset.sum_range_id]
    norm_num <;> simp [Finset.sum_range_succ] <;> ring

  have h_val_sum2 : ∑ k in Finset.range 5, (a + 2 * k) = 5 * a + 20 := by
    clear * - h_sum_k_5 h_sum_a_5 h_split_sum2
    simp_all only [Finset.sum_const, Finset.card_range, smul_eq_mul, reduceMul]

  have h_eq_subs : (64 : ℤ) - ↑(5 * a + 20) = (4 : ℤ) := by
    clear * - h₁ h_val_sum1 h_val_sum2
    simp_all only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul]

  have h_expand_sub : (64 : ℤ) - ↑(5 * a) - (20 : ℤ) = (4 : ℤ) := by
    clear * - h_eq_subs
    simp_all only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    (nlinarith)

  have h_simplify_eq : (44 : ℤ) - ↑(5 * a) = (4 : ℤ) := by
    clear * - h_expand_sub
    simp_all only [Nat.cast_mul, Nat.cast_ofNat]
    (nlinarith)

  have h_isolate_5a : ↑(5 * a) = (40 : ℤ) := by
    clear * - h_simplify_eq
    simp_all only [Nat.cast_mul, Nat.cast_ofNat]
    (nlinarith)

  have h_nat_5a : 5 * a = 40 := by
    clear * - h_isolate_5a
    simp_all only [Nat.cast_mul, Nat.cast_ofNat]
    (nlinarith)

  have h_final : a = 8 := by
    clear * - h_nat_5a
    (nlinarith)

  exact h_final