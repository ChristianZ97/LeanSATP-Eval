import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem induction_sumkexp3eqsumksq (n : ℕ) :
    (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
  induction n with
  | zero =>
    have h1 : (∑ k in Finset.range 0, k ^ 3) = 0 := by
      clear * -
      simp_all only [Finset.range_zero, Finset.sum_empty]

    have h2 : (∑ k in Finset.range 0, k) = 0 := by
      clear * -
      simp_all only [Finset.range_zero, Finset.sum_empty]

    have h3 : (∑ k in Finset.range 0, k) ^ 2 = 0 ^ 2 := by
      clear * - h2
      simp_all only [Finset.range_zero, Finset.sum_empty, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

    have h4 : 0 ^ 2 = 0 := by
      clear * -
      simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

    have h5 : (∑ k in Finset.range 0, k ^ 3) = (∑ k in Finset.range 0, k) ^ 2 := by
      clear * - h1 h3 h4
      simp_all only [Finset.range_zero, Finset.sum_empty, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

    exact h5

  | succ n ih =>
    have h7 : (∑ k in Finset.range (n + 1), k ^ 3) = (∑ k in Finset.range n, k ^ 3) + n ^ 3 := by
      clear * -
      apply Finset.sum_range_succ

    have h8 : (∑ k in Finset.range (n + 1), k ^ 3) = (∑ k in Finset.range n, k) ^ 2 + n ^ 3 := by
      clear * - h7 ih
      simp_all only

    have h9 : (∑ k in Finset.range (n + 1), k) = (∑ k in Finset.range n, k) + n := by
      clear * -
      rw [Finset.sum_range_succ, eq_comm]

    have h10 : ((∑ k in Finset.range n, k) + n) ^ 2 = (∑ k in Finset.range n, k) ^ 2 + 2 * n * (∑ k in Finset.range n, k) + n ^ 2 := by
      clear * -
      (nlinarith)

    have h11 : (∑ k in Finset.range n, k) = n * (n - (1 : ℕ)) / (2 : ℕ) := by
      clear * -
      induction n <;> simp [Finset.range_succ, *] at *
      induction ‹ℕ›
      ·
        simp_all only [Finset.range_zero, Finset.sum_empty, _root_.zero_le, Nat.sub_eq_zero_of_le, mul_zero, Nat.zero_div,
          add_zero, zero_add]
      · simp_all only [add_tsub_cancel_right]
        open Nat in ring_nf at * <;> omega

    have h12 : 2 * n * (∑ k in Finset.range n, k) = 2 * n * (n * (n - (1 : ℕ)) / (2 : ℕ)) := by
      clear * - h11
      simp_all only

    have h13 : 2 * n * (n * (n - (1 : ℕ)) / (2 : ℕ)) = n * (n * (n - (1 : ℕ))) := by
      clear * -
      cases n <;> simp [mul_assoc, mul_comm, mul_left_comm]
      rw [Nat.mul_div_cancel']
      · linarith only
      · obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd ‹_› <;> ring_nf <;> omega

    have h14 : n * (n * (n - (1 : ℕ))) = n ^ 3 - (n ^ 2 : ℕ) := by
      clear * -
      cases' n with n n
      ·
        simp_all only [_root_.zero_le, Nat.sub_eq_zero_of_le, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, tsub_self]
      · simp_all only [add_tsub_cancel_right]
        induction' n with n ih
        · simp_all only [zero_add, mul_zero, one_pow, tsub_self]
        · ring_nf
          omega

    have h15 : 2 * n * (∑ k in Finset.range n, k) = n ^ 3 - (n ^ 2 : ℕ) := by
      clear * - h11 h12 h13 h14
      simp_all only

    have h16 : ((∑ k in Finset.range n, k) + n) ^ 2 = (∑ k in Finset.range n, k) ^ 2 + (n ^ 3 - (n ^ 2 : ℕ)) + n ^ 2 := by
      clear * - h10 h15
      simp_all only

    have h17 : (n ^ 3 - (n ^ 2 : ℕ)) + n ^ 2 = n ^ 3 := by
      clear * -
      simp [pow_succ, sub_add_cancel]
      induction n <;> simp_all

    have h18 : ((∑ k in Finset.range n, k) + n) ^ 2 = (∑ k in Finset.range n, k) ^ 2 + n ^ 3 := by
      clear * - h16 h17
      simp_all only
      (nlinarith)

    have h19 : (∑ k in Finset.range (n + 1), k) ^ 2 = (∑ k in Finset.range n, k) ^ 2 + n ^ 3 := by
      clear * - h9 h18
      simp_all only

    have h20 : (∑ k in Finset.range (n + 1), k ^ 3) = (∑ k in Finset.range (n + 1), k) ^ 2 := by
      clear * - h8 h19
      simp_all only

    exact h20
