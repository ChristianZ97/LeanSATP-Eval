import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have h_step1 : (3 * a + b + c) + (a + 3 * b + c) + (a + b + 3 * c) = ((-3 : ℝ) + 9 + 19) := by
    clear * - h₀ h₁ h₂
    simp_all only

  have h_step2 : 5 * a + 5 * b + 5 * c = (25 : ℝ) := by
    clear * - h_step1
    (nlinarith)

  have h_step3 : 5 * (a + b + c) = (25 : ℝ) := by
    clear * - h_step2
    (nlinarith)

  have h_step4 : a + b + c = (5 : ℝ) := by
    clear * - h_step3
    (nlinarith)

  have h_step5 : 2 * a + (a + b + c) = (-3 : ℝ) := by
    clear * - h₀
    (nlinarith)

  have h_step6 : 2 * a + (5 : ℝ) = (-3 : ℝ) := by
    clear * - h_step5 h_step4
    simp_all only

  have h_step7 : 2 * a = (-8 : ℝ) := by
    clear * - h_step6
    (nlinarith)

  have h_step8 : a = (-4 : ℝ) := by
    clear * - h_step7
    (nlinarith)

  have h_step9 : (a + b + c) + 2 * b = (9 : ℝ) := by
    clear * - h₁
    (nlinarith)

  have h_step10 : (5 : ℝ) + 2 * b = (9 : ℝ) := by
    clear * - h_step9 h_step4
    simp_all only

  have h_step11 : 2 * b = (4 : ℝ) := by
    clear * - h_step10
    (nlinarith)

  have h_step12 : b = (2 : ℝ) := by
    clear * - h_step11
    (nlinarith)

  have h_step13 : (a + b + c) + 2 * c = (19 : ℝ) := by
    clear * - h₂
    (nlinarith)

  have h_step14 : (5 : ℝ) + 2 * c = (19 : ℝ) := by
    clear * - h_step13 h_step4
    simp_all only

  have h_step15 : 2 * c = (14 : ℝ) := by
    clear * - h_step14
    (nlinarith)

  have h_step16 : c = (7 : ℝ) := by
    clear * - h_step15
    (nlinarith)

  have h_step17 : a * b * c = ((-4 : ℝ) * 2 * 7) := by
    clear * - h_step8 h_step12 h_step16
    subst h_step8 h_step12 h_step16
    simp_all only [neg_mul]

  have h_step18 : a * b * c = (-56 : ℝ) := by
    clear * - h_step17
    simp_all only [neg_mul, neg_inj]
    (nlinarith)

  exact h_step18