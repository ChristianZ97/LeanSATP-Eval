import Mathlib
open BigOperators Real Nat Topology Rat
/-- Sally, Wei-Hwa, and Zoe are playing a game of marbles involving first arranging as many piles of 10 marbles as possible.  Sally brought 239 marbles, Wei-Hwa brought 174 marbles, and Zoe brought 83 marbles.  If all their marbles are grouped together, how many must be removed in order to start the game? Show that it is 6.-/

theorem mathd_numbertheory_254 : (239 + 174 + 83) % 10 = 6 := by

    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
  })
    (add safe 2 (by field_simp))
    (add safe 2 (by ring))
    (add safe 2 (by zify))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by norm_num [*] at *))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Nat.mul_mod_left | rw [Nat.mul_mod_left] | simp only [Nat.mul_mod_left]))
    (add unsafe 30% (by first | apply Nat.even_iff | rw [Nat.even_iff] | simp only [Nat.even_iff]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_one | rw [Nat.mod_two_ne_one] | simp only [Nat.mod_two_ne_one]))
    (add unsafe 30% (by first | apply Nat.mod_two_ne_zero | rw [Nat.mod_two_ne_zero] | simp only [Nat.mod_two_ne_zero]))
    (add unsafe 30% (by first | apply Nat.mul_mod | rw [Nat.mul_mod] | simp only [Nat.mul_mod]))
    (add unsafe 20% (by first | apply Nat.mul_mod_mod | rw [Nat.mul_mod_mod] | simp only [Nat.mul_mod_mod]))