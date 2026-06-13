import Mathlib
open BigOperators Real Nat Topology Rat
/-- Find the modulo 4 residue of $121 \cdot 122 \cdot 123$. Show that it is 2.-/

theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by

    aesop (config := {
    maxNormIterations       := 120
  })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply Nat.even_iff | rw [Nat.even_iff] | simp only [Nat.even_iff]))
    (add unsafe 40% (by first | apply Nat.mul_mod_left | rw [Nat.mul_mod_left] | simp only [Nat.mul_mod_left]))
    (add unsafe 30% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 30% (by first | apply Int.mul_emod | rw [Int.mul_emod] | simp only [Int.mul_emod]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 20% (by first | apply Int.odd_iff | rw [Int.odd_iff] | simp only [Int.odd_iff]))