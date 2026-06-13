import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_427 (a : ℕ) (h₀ : a = ∑ k in Nat.divisors 500, k) :
    (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = 25 := by
  have h_step_1 : 500 = 2^2 * 5^3 := by
    clear * -
    simp_all only [reducePow, reduceMul]

  have h_sigma_2_2_form : (∑ k in Nat.divisors (2^2), k) = (2^(2+1) - 1) / (2 - 1 : ℕ) := by
    clear * -
    simp_all only [reducePow, reduceAdd, Nat.add_one_sub_one, Nat.div_one]
    rfl

  have h_sigma_2_2_subst : (∑ k in Nat.divisors (2^2), k) = (2^3 - 1) / 1 := by
    clear * - h_sigma_2_2_form
    simp_all only [reducePow, reduceAdd, Nat.add_one_sub_one, Nat.div_one]

  have h_sigma_2_2_eval : (∑ k in Nat.divisors (2^2), k) = (8 - 1) / 1 := by
    clear * - h_sigma_2_2_subst
    simp_all only [reducePow, Nat.add_one_sub_one, Nat.div_one]

  have h_sigma_2_2_val : (∑ k in Nat.divisors (2^2), k) = 7 := by
    clear * - h_sigma_2_2_eval
    simp_all only [reducePow, Nat.add_one_sub_one, Nat.div_one]

  have h_sigma_5_3_form : (∑ k in Nat.divisors (5^3), k) = (5^(3+1) - 1) / (5 - 1 : ℕ) := by
    clear * -
    simp_all only [reducePow, reduceAdd, Nat.add_one_sub_one, reduceDiv]
    rfl

  have h_sigma_5_3_subst : (∑ k in Nat.divisors (5^3), k) = (5^4 - 1) / 4 := by
    clear * - h_sigma_5_3_form
    simp_all only [reducePow, reduceAdd, Nat.add_one_sub_one, reduceDiv]

  have h_sigma_5_3_eval : (∑ k in Nat.divisors (5^3), k) = (625 - 1) / 4 := by
    clear * - h_sigma_5_3_subst
    simp_all only [reducePow, Nat.add_one_sub_one, reduceDiv]

  have h_sigma_5_3_div : (∑ k in Nat.divisors (5^3), k) = 624 / 4 := by
    clear * - h_sigma_5_3_eval
    simp_all only [reducePow, Nat.add_one_sub_one, reduceDiv]

  have h_sigma_5_3_val : (∑ k in Nat.divisors (5^3), k) = 156 := by
    clear * - h_sigma_5_3_div
    simp_all only [reducePow, reduceDiv]

  have h_coprime_4_125 : Nat.Coprime (2^2) (5^3) := by
    clear * -
    simp_all only [reducePow]
    rfl

  have h_sum_mult : (∑ k in Nat.divisors 500, k) = (∑ k in Nat.divisors (2^2), k) * (∑ k in Nat.divisors (5^3), k) := by
    clear * - h_step_1 h_coprime_4_125
    simp_all only [reducePow, reduceMul]
    rfl

  have h_prod_1092 : (∑ k in Nat.divisors (2^2), k) * (∑ k in Nat.divisors (5^3), k) = 7 * 156 := by
    clear * - h_sigma_2_2_val h_sigma_5_3_val
    simp_all only [reducePow, reduceMul]

  have h_a_calc : a = 7 * 156 := by
    clear * - h₀ h_sum_mult h_prod_1092
    subst h₀
    simp_all only [reducePow, reduceMul]

  have h_a_val : a = 1092 := by
    clear * - h_a_calc
    subst h_a_calc
    simp_all only [reduceMul]

  have h_1092_1 : 1092 = 2 * 546 := by
    clear * -
    simp_all only [reduceMul]

  have h_546_1 : 546 = 2 * 273 := by
    clear * -
    simp_all only [reduceMul]

  have h_273_1 : 273 = 3 * 91 := by
    clear * -
    simp_all only [reduceMul]

  have h_91_1 : 91 = 7 * 13 := by
    clear * -
    simp_all only [reduceMul]

  have h_factors_explicit : 1092 = 2^2 * 3 * 7 * 13 := by
    clear * - h_1092_1 h_546_1 h_273_1 h_91_1
    simp_all only [reduceMul, reducePow]

  have h_primes_1092 : Finset.filter (fun x => Nat.Prime x) (Nat.divisors 1092) = {2, 3, 7, 13} := by
    clear * - h_factors_explicit
    simp_all only [reducePow, reduceMul]
    ext p
    simp_all only [Finset.mem_filter, mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true,
      Finset.mem_insert, Finset.mem_singleton]
    constructor <;> aesop
    · have : p ≤ 1092 := Nat.le_of_dvd (by norm_num) left
      interval_cases p <;> norm_num at *
    · use 546
    · exact Nat.prime_two
    · use 364
    · exact Nat.prime_three
    · use 156
    · exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl
    · use 84
    · decide

  have h_sum_primes_start : ∑ k in {2, 3, 7, 13}, k = 2 + 3 + 7 + 13 := by
    clear * -
    simp_all only [Finset.mem_insert, reduceEqDiff, Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
        Finset.sum_singleton, reduceAdd]

  have h_sum_primes_add1 : 2 + 3 + 7 + 13 = 5 + 7 + 13 := by
    clear * -
    simp_all only [reduceAdd]

  have h_sum_primes_add2 : 5 + 7 + 13 = 12 + 13 := by
    clear * -
    simp only [reduceAdd] at *

  have h_sum_primes_end : 12 + 13 = 25 := by
    clear * -
    simp only [reduceAdd] at *

  have h_total_sum_primes : ∑ k in {2, 3, 7, 13}, k = 25 := by
    clear * - h_sum_primes_start h_sum_primes_add1 h_sum_primes_add2 h_sum_primes_end
    simp_all only [Finset.mem_insert, reduceEqDiff, Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
        Finset.sum_singleton, reduceAdd]

  have h_substitute_primes : (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = ∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors 1092), k := by
    clear * - h_a_val
    subst h_a_val
    simp_all only

  have h_conclusion : (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = 25 := by
    clear * - h_substitute_primes h_primes_1092 h_total_sum_primes
    simp_all only [Finset.mem_insert, reduceEqDiff, Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
        Finset.sum_singleton, reduceAdd]

  exact h_conclusion
