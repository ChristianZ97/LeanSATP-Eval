import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  have h1 : 4 ^ (n + 1) = 4 * 4 ^ n := by
    clear * -
    (omega)

  have h2 : 4 ^ (n + 1) + 20 = 4 * 4 ^ n + 20 := by
    clear * - h1
    simp_all only

  have h3 : 4 * 4 ^ n + 20 = 4 * ((4 ^ n : ℕ) - 1 + 1) + 20 := by
    clear * -
    simp_all only [add_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
    cases n <;> simp [pow_succ] <;> ring_nf
    zify [pow_succ]
    simp_all only [ofNat_pos, mul_pos_iff_of_pos_right, pow_pos, cast_pred, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      add_sub_cancel]

  have h4 : 4 * ((4 ^ n : ℕ) - 1 + 1) + 20 = 4 * ((4 ^ n : ℕ) - 1) + 4 + 20 := by
    clear * -
    simp_all only [add_left_inj]
    rfl

  have h5 : 4 * ((4 ^ n : ℕ) - 1) + 4 + 20 = 4 * ((4 ^ n : ℕ) - 1) + 24 := by
    clear * -
    simp_all only

  have h6 : (3 : ℤ) ∣ (4 ^ n - 1 : ℤ) := by
    clear * -
    induction' n with n b_h
    · simp_all only [pow_zero, sub_self, dvd_zero]
    · simp [pow_succ, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at *
      have _ := b_h
      simp_all only
      induction' n with n ih <;> simp [*, pow_succ] at * <;> omega

  have h7 : ∃ (k : ℤ), (4 ^ n : ℤ) - 1 = 3 * k := by
    clear * - h6
    exact h6

  have h8 : ∀ (k : ℤ), (4 ^ n : ℤ) - 1 = 3 * k →
      (4 : ℤ) * ((4 ^ n : ℤ) - 1) + 24 = 12 * (k + 2) := by
    clear * -
    intro k a
    simp_all only
    (nlinarith)

  have h9 : (12 : ℤ) ∣ ((4 : ℤ) * ((4 ^ n : ℤ) - 1) + 24 : ℤ) := by
    clear * - h7 h8
    simp_all only
    obtain ⟨w, h⟩ := h7
    simp_all only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, forall_eq', dvd_mul_right]

  have h10 : 12 ∣ 4 ^ (n + 1) + 20 := by
    clear * - h2 h3 h4 h5 h9
    simp_all only [add_left_inj, Nat.dvd_add_self_right]
    (ring_nf at *)
    simp_all only
    (norm_cast at *)
    simp_all only
    (omega)

  exact h10
