import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  have h1 : 4 ^ (n + 1) = 4 * 4 ^ n := by
    clear * -
    (omega)

  have h2 : 4 ^ (n + 1) + 20 = 4 * 4 ^ n + 20 := by
    clear * - h1
    simp_all only [Nat.add_left_cancel_iff]

  have h3 : 4 * 4 ^ n + 20 = 4 * ((4 ^ n : ℕ) - 1 + 1) + 20 := by
    clear * -
    ring_nf
    induction n <;> simp [pow_succ, mul_add] <;> omega

  have h4 : 4 * ((4 ^ n : ℕ) - 1 + 1) + 20 = 4 * ((4 ^ n : ℕ) - 1) + 4 + 20 := by
    clear * -
    simp_all only [Nat.add_right_cancel_iff]
    (linarith)

  have h5 : 4 * ((4 ^ n : ℕ) - 1) + 4 + 20 = 4 * ((4 ^ n : ℕ) - 1) + 24 := by
    clear * -
    simp_all only [Nat.add_right_cancel_iff, Nat.add_left_cancel_iff]

  have h6 : (3 : ℤ) ∣ (4 ^ n - 1 : ℤ) := by
    clear * -
    induction' n with n PN
    · norm_num
    · simp [pow_succ, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at * <;> omega

  have h7 : ∃ (k : ℤ), (4 ^ n : ℤ) - 1 = 3 * k := by
    clear * - h6
    exact h6

  have h8 : ∀ (k : ℤ), (4 ^ n : ℤ) - 1 = 3 * k →
      (4 : ℤ) * ((4 ^ n : ℤ) - 1) + 24 = 12 * (k + 2) := by
    clear * -
    simp_all only
    (omega)

  have h9 : (12 : ℤ) ∣ ((4 : ℤ) * ((4 ^ n : ℤ) - 1) + 24 : ℤ) := by
    clear * - h7 h8
    simp_all only
    (omega)

  have h10 : 12 ∣ 4 ^ (n + 1) + 20 := by
    clear * - h2 h3 h4 h5 h9
    simp_all only [Nat.add_right_cancel_iff, Nat.add_left_cancel_iff, Nat.dvd_add_self_right]
    (grind only [dvd_mul_left])

  exact h10
