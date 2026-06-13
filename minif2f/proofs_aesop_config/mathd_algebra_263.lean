import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_263 (y : ℝ) (h₀ : 0 ≤ 19 + 3 * y) (h₁ : Real.sqrt (19 + 3 * y) = 7) :
    y = 10 := by
  have h2 : (Real.sqrt (19 + 3 * y))^2 = 7^2 := by
    clear * - h₁
    simp_all only

  have h3 : 19 + 3 * y = 7^2 := by
    clear * - h2 h₀
    simp_all only [sq_sqrt]

  have h4 : 19 + 3 * y = 49 := by
    clear * - h3
    simp_all only
    (nlinarith)

  have h5 : 3 * y = (49 : ℝ) - (19 : ℝ) := by
    clear * - h4
    (nlinarith)

  have h6 : 3 * y = 30 := by
    clear * - h5
    simp_all only
    (nlinarith)

  have h7 : y = (30 : ℝ) / (3 : ℝ) := by
    clear * - h6
    (field_simp)
    (nlinarith)

  have h8 : y = 10 := by
    clear * - h7
    subst h7
    (field_simp)
    (nlinarith)

  exact h8