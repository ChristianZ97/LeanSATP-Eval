import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have h1 : 0 ≤ ((a - b) - 1) ^ 2 := by
    clear * -
    (nlinarith)

  have h2 : 0 ≤ (a - b) ^ 2 - 2 * (a - b) + 1 := by
    clear * - h1
    (nlinarith)

  have h3 : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 - 2 * a + 2 * b + 1 := by
    clear * - h2
    (nlinarith)

  have h4 : 0 ≤ (a ^ 2 + b ^ 2) - 2 * a * b - 2 * a + 2 * b + 1 := by
    clear * - h3
    (nlinarith)

  have h5 : 0 ≤ 1 - 2 * a * b - 2 * a + 2 * b + 1 := by
    clear * - h4 h₀
    simp_all only

  have h6 : 0 ≤ 2 - 2 * a * b - 2 * a + 2 * b := by
    clear * - h5
    (nlinarith)

  have h7 : 2 * a * b + 2 * a - 2 * b ≤ 2 := by
    clear * - h6
    simp_all only [tsub_le_iff_right]
    (nlinarith)

  have h8 : 2 * (a * b + a - b) ≤ 2 := by
    clear * - h7
    simp_all only [tsub_le_iff_right, ofNat_pos, mul_le_iff_le_one_right]
    (nlinarith)

  have h9 : a * b + (a - b) ≤ 1 := by
    clear * - h8
    simp_all only [ofNat_pos, mul_le_iff_le_one_right, tsub_le_iff_right]
    (nlinarith)

  exact h9