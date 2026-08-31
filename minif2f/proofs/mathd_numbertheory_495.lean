import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_numbertheory_495 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a % 10 = 2) (h₂ : b % 10 = 4)
    (h₃ : Nat.gcd a b = 6) : 108 ≤ Nat.lcm a b := by
  have h_lcm_mul_gcd : Nat.lcm a b * Nat.gcd a b = a * b := by
    clear * -
    simp_all only [lcm_mul_gcd]

  have h_lcm_times_6 : Nat.lcm a b * 6 = a * b := by
    clear * - h₃ h_lcm_mul_gcd
    simp_all only

  have h_gcd_div_a : Nat.gcd a b ∣ a := by
    clear * -
    apply Nat.gcd_dvd_left

  have h_6_div_a : 6 ∣ a := by
    clear * - h₃ h_gcd_div_a
    simp_all only

  have h_gcd_div_b : Nat.gcd a b ∣ b := by
    clear * -
    rw [Nat.gcd_comm]
    rw [gcd_comm]
    rw [Nat.gcd_comm]
    apply Nat.gcd_dvd_left

  have h_6_div_b : 6 ∣ b := by
    clear * - h₃ h_gcd_div_b
    simp_all only

  let u : ℕ := a / 6
  let v : ℕ := b / 6
  have h_a_eq_6u : a = 6 * u := by
    clear * - h_6_div_a
    simp_all only [u]
    (omega)

  have h_b_eq_6v : b = 6 * v := by
    clear * - h_6_div_b
    simp_all only [v]
    (omega)

  have h_ab_eq_36uv : a * b = 36 * u * v := by
    clear * - h_a_eq_6u h_b_eq_6v
    rewrite [h_a_eq_6u, h_b_eq_6v] <;> (ring)

  have h_u_mod_5 : u % 5 = 2 := by
    clear * - h_a_eq_6u h₁
    rewrite [h_a_eq_6u, Nat.mul_mod] at h₁
    revert h₁ u <;> omega

  have h_v_mod_5 : v % 5 = 4 := by
    clear * - h_b_eq_6v h₂
    omega

  have h_u_pos : 0 < u := by
    clear * - h₀ h_a_eq_6u
    valid

  have h_v_pos : 0 < v := by
    clear * - h₀ h_b_eq_6v
    cases h₀ with
    | intro _ h₁ => omega

  have h_gcd_uv : Nat.gcd u v = 1 := by
    clear * - h₃ h_a_eq_6u h_b_eq_6v
    by_contra
    have h_gcd : a.gcd b = 6 * (u.gcd v)
    · simp_all [Nat.gcd_mul_left, Nat.gcd_comm]
    · simp_all

  have h_u_ge_2 : 2 ≤ u := by
    clear * - h_u_pos h_u_mod_5
    simp_all only [Nat.div_pos_iff, ofNat_pos, true_and, u]
    (omega)

  have h_v_ge_4 : 4 ≤ v := by
    clear * - h_v_pos h_v_mod_5
    simp_all only [Nat.div_pos_iff, ofNat_pos, true_and, v]
    (omega)

  have h_u_cases : u = 2 ∨ 7 ≤ u := by
    clear * - h_u_ge_2 h_u_mod_5
    simp_all only [u]
    (omega)

  have h_u2_imp_v_ge_9 : u = 2 → 9 ≤ v := by
    clear * - h_gcd_uv h_v_mod_5 h_v_pos
    intros h_u_eq_2
    by_contra h_lt_9
    interval_cases v <;> simp_all (config := { decide := true })

  have h_u7_imp_uv_ge_28 : 7 ≤ u → 28 ≤ u * v := by
    clear * - h_v_ge_4
    intro a_1
    simp_all only [v, u]
    (nlinarith)

  have h_uv_ge_18 : 18 ≤ u * v := by
    clear * - h_u_cases h_u2_imp_v_ge_9 h_u7_imp_uv_ge_28
    simp_all only [u, v]
    (grind only [le_of_mul_le_mul_left])

  have h_ab_ge_648 : 648 ≤ a * b := by
    clear * - h_ab_eq_36uv h_uv_ge_18
    simp only [u, v] at *
    (linarith)

  have h_lcm_times_6_ge_648 : Nat.lcm a b * 6 ≥ 648 := by
    clear * - h_lcm_times_6 h_ab_ge_648
    simp_all only [ge_iff_le]

  have h_final : 108 ≤ Nat.lcm a b := by
    clear * - h_lcm_times_6_ge_648
    simp_all only [ge_iff_le]
    (linarith)

  exact h_final
