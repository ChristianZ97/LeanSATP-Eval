import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h1 : (21 * n + 4 : ℕ) - (14 * n + 3) = 7 * n + 1 := by
    clear * - h₀
    simp_all only [reduceSubDiff]
    (omega)

  have h2 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
    clear * - h1
    simp_all only [reduceSubDiff]
    by_cases m : 7 * n + 1 = 0
    ·
      simp_all only [AddLeftCancelMonoid.add_eq_zero, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or, one_ne_zero,
        and_false]
    · simp_all only [AddLeftCancelMonoid.add_eq_zero, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or, one_ne_zero,
        and_false, not_false_eq_true]
      have h2 : (21 * n + 4) = (14 * n + 3) + (7 * n + 1) := by ring
      simp_all only [gcd_self_add_left]
      rw [Nat.gcd_comm]

  have h3 : (14 * n + 3 : ℕ) - 2 * (7 * n + 1) = 1 := by
    clear * - h₀
    (omega)

  have h4 : Nat.gcd (14 * n + 3) (7 * n + 1) = Nat.gcd (7 * n + 1) 1 := by
    clear * - h3
    simp_all only [Nat.gcd_one_right]
    simp [(show 14 * n + 3 = 2 * (7 * n + 1) + 1 by omega)]

  have h5 : Nat.gcd (7 * n + 1) 1 = 1 := by
    clear * -
    simp_all only [Nat.gcd_one_right]

  have h6 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    clear * - h2 h4 h5
    simp_all only [Nat.gcd_one_right]

  exact h6
