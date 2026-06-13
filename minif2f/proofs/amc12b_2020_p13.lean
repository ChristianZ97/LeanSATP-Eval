import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12b_2020_p13 :
    Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) =
      Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
  have h1 : (Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3))^2 = Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 := by
    clear * -
    (field_simp)
    (ring_nf at *)
    (field_simp)

  have h2 : Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 = Real.log (2 * 3) / Real.log 2 + Real.log (2 * 3) / Real.log 3 := by
    clear * -
    (field_simp)
    (norm_num [*] at *)

  have h3 : Real.log (2 * 3) / Real.log 2 + Real.log (2 * 3) / Real.log 3 = (Real.log 2 + Real.log 3) / Real.log 2 + (Real.log 2 + Real.log 3) / Real.log 3 := by
    clear * -
    repeat rw [Real.log_mul]
    · simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    · simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

  have h4 : (Real.log 2 + Real.log 3) / Real.log 2 + (Real.log 2 + Real.log 3) / Real.log 3 = (Real.log 2 / Real.log 2 + Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3 + Real.log 3 / Real.log 3) := by
    clear * -
    (field_simp)

  have h5 : (Real.log 2 / Real.log 2 + Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3 + Real.log 3 / Real.log 3) = (1 + Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3 + 1) := by
    clear * -
    (field_simp)

  have h6 : (1 + Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3 + 1) = Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 := by
    clear * -
    (field_simp)
    (nlinarith)

  have h7 : (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3))^2 = Real.log 3 / Real.log 2 + 2 * Real.sqrt ((Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3)) + Real.log 2 / Real.log 3 := by
    clear * -
    (field_simp)
    (ring_nf at *)
    (field_simp)
    (nlinarith)

  have h8 : Real.log 3 / Real.log 2 + 2 * Real.sqrt ((Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3)) + Real.log 2 / Real.log 3 = Real.log 3 / Real.log 2 + 2 * Real.sqrt 1 + Real.log 2 / Real.log 3 := by
    clear * -
    simp_all only [Real.sqrt_one, mul_one, add_left_inj, add_right_inj, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_eq_left₀, sqrt_eq_one]
    (field_simp)

  have h9 : Real.log 3 / Real.log 2 + 2 * Real.sqrt 1 + Real.log 2 / Real.log 3 = Real.log 3 / Real.log 2 + 2 + Real.log 2 / Real.log 3 := by
    clear * -
    simp_all only [Real.sqrt_one, mul_one]

  have h10 : Real.log 3 / Real.log 2 + 2 + Real.log 2 / Real.log 3 = Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 := by
    clear * -
    (field_simp)
    (nlinarith)

  have h11 : (Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3))^2 = (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3))^2 := by
    clear * - h1 h3 h4 h5 h6 h7 h8 h9 h10
    simp_all only [Real.sqrt_one, mul_one]
    (field_simp)
    (norm_num [*] at *)
    simp_all only
    (field_simp [*] at *)
    simp_all only

  have h12 : Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
    clear * - h11
    (field_simp)
    (field_simp [*] at *)
    simp_all only
    (field_simp)

  exact h12