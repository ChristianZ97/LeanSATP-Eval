import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  have h1 : (10 : ℤ) = (11 : ℤ) + (-1 : ℤ) := by
    clear * -
    simp_all only [Int.reduceNeg, Int.reduceAdd]

  have h2 : (10 : ℤ) ^ n = ((11 : ℤ) + (-1 : ℤ)) ^ n := by
    clear * - h1
    simp_all only [Int.reduceNeg, Int.reduceAdd]

  have h3 : ((11 : ℤ) + (-1 : ℤ)) ^ n = ∑ k in Finset.range (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) := by
    clear * -
    simp_all only [Int.reduceNeg, Int.reduceAdd]
    have A := (add_pow 11 (-1) n).symm
    simp_all only [Int.reduceNeg, Int.reduceAdd]
    nth_rewrite 1 [← A]
    simp_all only [Int.reduceNeg]
    simp [← A, mul_comm, mul_assoc, mul_left_comm, ← mul_add]

  have h4 : ((11 : ℤ) + (-1 : ℤ)) ^ n = (Nat.choose n 0 : ℤ) * (11 : ℤ) ^ 0 * (-1 : ℤ) ^ n + ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) := by
    clear * - h3
    simp_all only [Int.reduceNeg, Int.reduceAdd, choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul]
    simp [Finset.sum_Ico_eq_sub, ← h3]

  have h5 : (Nat.choose n 0 : ℤ) * (11 : ℤ) ^ 0 * (-1 : ℤ) ^ n = (-1 : ℤ) ^ n := by
    clear * -
    simp_all only [choose_zero_right, Nat.cast_one, pow_zero, mul_one, Int.reduceNeg, one_mul]

  have h6 : (10 : ℤ) ^ n = (-1 : ℤ) ^ n + ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) := by
    clear * - h2 h4 h5
    simp_all only [Int.reduceNeg, Int.reduceAdd, choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul]

  have h7 : (10 : ℤ) ^ n - (-1 : ℤ) ^ n = ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) := by
    clear * - h6
    simp_all only [Int.reduceNeg, add_sub_cancel_left]

  have h8 : ∀ k ∈ Finset.Ico 1 (n + 1), (11 : ℤ) ^ k = (11 : ℤ) * (11 : ℤ) ^ (k - 1) := by
    clear * -
    simp_all
    intro k _ hk2
    cases k <;> simp [pow_succ]
    · simp_all
    · simp_all
      rw [mul_comm]

  have h9 : ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) = ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) * (11 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (n - k) := by
    clear * - h8
    simp_all
    refine' Finset.sum_congr rfl _
    simp_all
    simp [mul_assoc, mul_left_comm] <;> intros <;> aesop

  have h10 : ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) * (11 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (n - k) = (11 : ℤ) * ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (n - k) := by
    clear * - h9
    clear h9
    simp [Finset.mul_sum, mul_assoc, Nat.cast_comm]

  have h11 : (10 : ℤ) ^ n - (-1 : ℤ) ^ n = (11 : ℤ) * ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (n - k) := by
    clear * - h7 h9 h10
    simp_all only [Int.reduceNeg]

  have h12 : ∃ (m : ℤ), (10 : ℤ) ^ n - (-1 : ℤ) ^ n = (11 : ℤ) * m := by
    clear * - h11
    simp_all only [Int.reduceNeg, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq']

  have h13 : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
    clear * - h12
    obtain ⟨w, h⟩ := h12
    simp_all only [Int.reduceNeg, dvd_mul_right]

  exact h13
