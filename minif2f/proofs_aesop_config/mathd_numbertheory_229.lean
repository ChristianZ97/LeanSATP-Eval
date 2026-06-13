import Mathlib
open BigOperators Real Nat Topology Rat
/-- What is the remainder when $5^{30}$ is divided by 7? Show that it is 1.-/

theorem mathd_numbertheory_229 : 5 ^ 30 % 7 = 1 := by

    aesop (config := {
    maxNormIterations       := 120
  })
    (add safe 1 (by ring))
    (add safe 2 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf))
    (add unsafe 40% (by first | apply Int.emod_emod_of_dvd | rw [Int.emod_emod_of_dvd] | simp only [Int.emod_emod_of_dvd]))
    (add unsafe 40% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 30% (by first | apply GaussianInt.mod_four_eq_three_of_nat_prime_of_prime | rw [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] | simp only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
    (add unsafe 30% (by first | apply Int.mul_emod | rw [Int.mul_emod] | simp only [Int.mul_emod]))
    (add unsafe 30% (by first | apply Int.natCast_mod | rw [Int.natCast_mod] | simp only [Int.natCast_mod]))
    (add unsafe 20% (by first | apply Int.ModEq | rw [Int.ModEq] | simp only [Int.ModEq]))
    (add unsafe 20% (by first | apply Int.emod_emod | rw [Int.emod_emod] | simp only [Int.emod_emod]))