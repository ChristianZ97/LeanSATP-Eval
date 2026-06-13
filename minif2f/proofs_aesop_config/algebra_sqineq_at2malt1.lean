import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h1 : a * (2 - a) = 2 * a - a ^ 2 := by
    clear * -
    (nlinarith)

  have h2 : 1 - a * (2 - a) = 1 - (2 * a - a ^ 2) := by
    clear * - h1
    simp_all only

  have h3 : 1 - (2 * a - a ^ 2) = 1 - 2 * a + a ^ 2 := by
    clear * -
    (nlinarith)

  have h4 : 1 - 2 * a + a ^ 2 = (a - 1) ^ 2 := by
    clear * -
    (nlinarith)

  have h5 : (a - 1) ^ 2 ≥ 0 := by
    clear * -
    simp_all only [ge_iff_le]
    (nlinarith)

  have h6 : 1 - a * (2 - a) ≥ 0 := by
    clear * - h2 h3 h4 h5
    simp_all only [ge_iff_le]

  have h7 : a * (2 - a) ≤ 1 := by
    clear * - h6
    simp_all only [ge_iff_le, sub_nonneg]

  exact h7