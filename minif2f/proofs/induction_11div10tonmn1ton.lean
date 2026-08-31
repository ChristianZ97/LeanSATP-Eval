import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  have h_step1 : (10 : ℤ) ^ n - (-1 : ℤ) ^ n = ((10 : ℤ) - (-1 : ℤ)) * (∑ i in Finset.range n, (10 : ℤ) ^ (n - 1 - i) * (-1 : ℤ) ^ i) := by
    clear * -
    induction' n with n ih <;> simp [Finset.sum_range_succ']
    simp [pow_succ, mul_add, mul_comm, mul_left_comm]
    induction' n with bn bih
    · simp [-Nat.succ_eq_add_one]
    · cases' bn with bn <;> simp_all [Finset.sum_range_succ'] <;> ring_nf at * <;> omega

  have h_step2 : (10 : ℤ) - (-1 : ℤ) = 11 := by
    clear * -
    simp_all only [Int.reduceNeg, sub_neg_eq_add, Int.reduceAdd]

  have h_step3 : (10 : ℤ) ^ n - (-1 : ℤ) ^ n = 11 * (∑ i in Finset.range n, (10 : ℤ) ^ (n - 1 - i) * (-1 : ℤ) ^ i) := by
    clear * - h_step1 h_step2
    simp_all only [Int.reduceNeg, sub_neg_eq_add, Int.reduceAdd]

  let k : ℤ := ∑ i in Finset.range n, (10 : ℤ) ^ (n - 1 - i) * (-1 : ℤ) ^ i

  have h_step4 : (10 : ℤ) ^ n - (-1 : ℤ) ^ n = 11 * k := by
    clear * - h_step3
    simp_all only [Int.reduceNeg, k]

  have h_step5 : 11 ∣ (10 : ℤ) ^ n - (-1 : ℤ) ^ n := by
    clear * - h_step4
    simp_all only [Int.reduceNeg, dvd_mul_right, k]

  exact h_step5
