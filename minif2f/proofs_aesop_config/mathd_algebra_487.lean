import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have h5 : a + a ^ 2 = (1:ℝ) := by
    clear * - h₀ h₁
    subst h₀
    simp_all only

  have h6 : c + c ^ 2 = (1:ℝ) := by
    clear * - h₂ h₃
    subst h₂
    simp_all only

  have h7 : a ^ 2 + a - (1:ℝ) = 0 := by
    clear * - h5
    (nlinarith)

  have h8 : c ^ 2 + c - (1:ℝ) = 0 := by
    clear * - h6
    (nlinarith)

  have h9 : a + c = -(1:ℝ) := by
    clear * - h7 h8 h₄
    simp_all only [ne_eq]
    apply mul_right_cancel₀ (sub_ne_zero_of_ne <| h₄) <;> nlinarith [sq_nonneg (a - c)]

  have h10 : a * c = -(1:ℝ) := by
    clear * - h7 h8 h₄
    simp_all only [ne_eq]
    nlinarith [sq_nonneg (a - c), mul_self_pos.2 (sub_ne_zero.2 h₄)]

  have h11 : (a - c) ^ 2 = (a + c) ^ 2 - (4:ℝ) * (a * c) := by
    clear * -
    (nlinarith)

  have h12 : (a - c) ^ 2 = (-(1:ℝ)) ^ 2 - (4:ℝ) * (-(1:ℝ)) := by
    clear * - h9 h10 h11
    simp_all only [even_two, Even.neg_pow, one_pow, mul_neg, mul_one, sub_neg_eq_add]

  have h13 : (a - c) ^ 2 = (1:ℝ) - (4:ℝ) * (-(1:ℝ)) := by
    clear * - h12
    simp_all only [even_two, Even.neg_pow, one_pow, mul_neg, mul_one, sub_neg_eq_add]

  have h14 : (a - c) ^ 2 = (1:ℝ) - (-(4:ℝ)) := by
    clear * - h13
    simp_all only [mul_neg, mul_one, sub_neg_eq_add]

  have h15 : (a - c) ^ 2 = (1:ℝ) + (4:ℝ) := by
    clear * - h14
    simp_all only [sub_neg_eq_add]

  have h16 : (a - c) ^ 2 = (5:ℝ) := by
    clear * - h15
    simp_all only
    (nlinarith)

  have h17 : b = (1:ℝ) - a := by
    clear * - h₀ h₁
    subst h₀
    (nlinarith)

  have h18 : d = (1:ℝ) - c := by
    clear * - h₂ h₃
    subst h₂
    (nlinarith)

  have h19 : b - d = ((1:ℝ) - a) - ((1:ℝ) - c) := by
    clear * - h17 h18
    subst h18 h17
    simp_all only [sub_sub_sub_cancel_left]

  have h20 : b - d = (1:ℝ) - a - (1:ℝ) + c := by
    clear * - h19
    simp_all only [sub_sub_sub_cancel_left, sub_sub_cancel_left]
    (nlinarith)

  have h21 : b - d = c - a := by
    clear * - h20
    simp_all only [sub_sub_cancel_left]
    (nlinarith)

  have h22 : (b - d) ^ 2 = (c - a) ^ 2 := by
    clear * - h21
    simp_all only

  have h23 : (b - d) ^ 2 = (a - c) ^ 2 := by
    clear * - h22
    simp_all only
    (nlinarith)

  have h24 : (b - d) ^ 2 = (5:ℝ) := by
    clear * - h16 h23
    simp_all only

  have h25 : (a - c) ^ 2 + (b - d) ^ 2 = (5:ℝ) + (5:ℝ) := by
    clear * - h16 h24
    simp_all only

  have h26 : (a - c) ^ 2 + (b - d) ^ 2 = (10:ℝ) := by
    clear * - h25
    simp_all only
    (nlinarith)

  have h27 : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt (10:ℝ) := by
    clear * - h26
    simp_all only

  exact h27