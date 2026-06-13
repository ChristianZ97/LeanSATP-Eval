import Mathlib
open BigOperators Real Nat Topology Rat
/-- What is the remainder when $2000+2001+2002+2003+2004+2005+2006$ is divided by $7$? Show that it is 0.-/

theorem mathd_numbertheory_345 : (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7 = 0 := by

    aesop (config := {
    maxNormIterations       := 120
  })
    (add safe 2 (by ring))
    (add safe 2 (by zify))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 40% (by first | apply Nat.odd_iff | rw [Nat.odd_iff] | simp only [Nat.odd_iff]))
    (add unsafe 30% (by first | apply Nat.even_iff | rw [Nat.even_iff] | simp only [Nat.even_iff]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 30% (by first | apply Nat.mul_mod | rw [Nat.mul_mod] | simp only [Nat.mul_mod]))
    (add unsafe 30% (by first | apply Nat.mul_mod_left | rw [Nat.mul_mod_left] | simp only [Nat.mul_mod_left]))