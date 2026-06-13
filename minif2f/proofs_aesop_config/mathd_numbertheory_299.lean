import Mathlib
open BigOperators Real Nat Topology Rat
/-- What is the ones digit of $1 \cdot 3 \cdot 5 \cdot 7 \cdot 9 \cdot 11 \cdot 13$? Show that it is 5.-/

theorem mathd_numbertheory_299 : 1 * 3 * 5 * 7 * 9 * 11 * 13 % 10 = 5 := by

    aesop (config := {
    maxNormIterations       := 120
  })
    (add safe 2 (by ring))
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Nat.even_iff | rw [Nat.even_iff] | simp only [Nat.even_iff]))
    (add unsafe 40% (by first | apply Nat.mul_mod_left | rw [Nat.mul_mod_left] | simp only [Nat.mul_mod_left]))
    (add unsafe 30% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 30% (by first | apply Int.mul_emod | rw [Int.mul_emod] | simp only [Int.mul_emod]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 20% (by first | apply Int.odd_iff | rw [Int.odd_iff] | simp only [Int.odd_iff]))