import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem aime_1990_p15 (a b x y : ℝ) (h₀ : a * x + b * y = 3) (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16) (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by
  let u := x + y

  let v := x * y

  have h_step3 : a * x ^ 3 + b * y ^ 3 = u * (a * x ^ 2 + b * y ^ 2) - v * (a * x + b * y) := by
    clear * -
    simp_all only [u, v]
    (nlinarith)

  have h_step4 : (16 : ℝ) = 7 * u - 3 * v := by
    clear * - h_step3 h₂ h₁ h₀
    simp_all only [u, v]
    (nlinarith)

  have h_step5 : a * x ^ 4 + b * y ^ 4 = u * (a * x ^ 3 + b * y ^ 3) - v * (a * x ^ 2 + b * y ^ 2) := by
    clear * -
    simp_all only [u, v]
    (nlinarith)

  have h_step6 : (42 : ℝ) = 16 * u - 7 * v := by
    clear * - h_step5 h₃ h₂ h₁
    simp_all only [u, v]
    (nlinarith)

  have h_step7 : (112 : ℝ) = 49 * u - 21 * v := by
    clear * - h_step4
    simp_all only [u, v]
    (nlinarith)

  have h_step8 : (126 : ℝ) = 48 * u - 21 * v := by
    clear * - h_step6
    simp_all only [u, v]
    (nlinarith)

  have h_step9 : (49 * u - 21 * v) - (48 * u - 21 * v) = (112 : ℝ) - (126 : ℝ) := by
    clear * - h_step7 h_step8
    simp_all only [sub_sub_sub_cancel_right, u, v]

  have h_step10 : u = (-14 : ℝ) := by
    clear * - h_step9
    simp_all only [sub_sub_sub_cancel_right, u, v]
    (nlinarith)

  have h_step11 : (16 : ℝ) = 7 * (-14 : ℝ) - 3 * v := by
    clear * - h_step4 h_step10
    simp_all only [mul_neg, u, v]

  have h_step12 : (16 : ℝ) = (-98 : ℝ) - 3 * v := by
    clear * - h_step11
    simp_all only [mul_neg, sub_left_inj, neg_inj, v]
    (nlinarith)

  have h_step13 : (114 : ℝ) = -3 * v := by
    clear * - h_step12
    simp_all only [neg_mul, v]
    (nlinarith)

  have h_step14 : v = (-38 : ℝ) := by
    clear * - h_step13
    simp_all only [neg_mul, v]
    (nlinarith)

  have h_step15 : a * x ^ 5 + b * y ^ 5 = u * (a * x ^ 4 + b * y ^ 4) - v * (a * x ^ 3 + b * y ^ 3) := by
    clear * -
    simp_all only [u, v]
    (nlinarith)

  have h_step16 : a * x ^ 5 + b * y ^ 5 = (-14 : ℝ) * (42 : ℝ) - (-38 : ℝ) * (16 : ℝ) := by
    clear * - h_step15 h_step10 h_step14 h₃ h₂
    simp_all only [neg_mul, sub_neg_eq_add, u, v]

  have h_step17 : a * x ^ 5 + b * y ^ 5 = (-588 : ℝ) + (608 : ℝ) := by
    clear * - h_step16
    simp_all only [neg_mul, sub_neg_eq_add]
    (nlinarith)

  have h_step18 : a * x ^ 5 + b * y ^ 5 = (20 : ℝ) := by
    clear * - h_step17
    simp_all only
    (nlinarith)

  exact h_step18