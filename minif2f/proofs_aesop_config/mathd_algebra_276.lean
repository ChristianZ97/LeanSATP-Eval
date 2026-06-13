import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_276 (a b : ℤ)
    (h₀ : ∀ x : ℝ, 10 * x ^ 2 - x - 24 = (a * x - 8) * (b * x + 3)) : a * b + b = 12 := by
  have h_expand : ∀ x : ℝ, (a : ℝ) * (b : ℝ) * x ^ 2 + (3 * (a : ℝ) - 8 * (b : ℝ)) * x - 24 = (a * x - 8) * (b * x + 3) := by
    clear * -
    intro x
    (nlinarith)

  have h_coeff_sq : (a : ℝ) * (b : ℝ) = 10 := by
    clear * - h₀ h_expand
    let h₁ := h_expand (-1)
    let h₂ := h_expand (-2)
    nlinarith [h₀ 0, h₀ 1, h₀ 2]

  have h_coeff_x : 3 * (a : ℝ) - 8 * (b : ℝ) = -1 := by
    clear * - h₀ h_expand
    have eq₁ := h_expand 1
    simp_all only [one_pow, mul_one]
    simp [mul_comm] at *
    simp_all [sq]
    linarith [h₀ (-2), h₀ (-3 / 2), h₀ (-1), h₀ (-1 / 2), h₀ (-4)]

  have h_prod_int : a * b = 10 := by
    clear * - h_coeff_sq
    (norm_cast at *)

  have h_lin_int : 3 * a - 8 * b = -1 := by
    clear * - h_coeff_x
    (norm_cast at *)

  have h_a_ne_zero : a ≠ 0 := by
    clear * - h_prod_int
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    simp_all only [zero_mul, OfNat.zero_ne_ofNat]

  have h_quadratic_eq : 3 * a ^ 2 + a - 80 = 0 := by
    clear * - h_lin_int h_prod_int h_a_ne_zero
    simp_all only [Int.reduceNeg, ne_eq]
    (nlinarith)

  have h_factored : (3 * a + 16) * (a - 5) = 0 := by
    clear * - h_quadratic_eq
    simp_all only [_root_.mul_eq_zero]
    have : a ≤ 10 := by nlinarith
    on_goal 1 =>
    have : a ≥ -10 := by nlinarith
    interval_cases a <;> omega

  have h_options : 3 * a + 16 = 0 ∨ a - 5 = 0 := by
    clear * - h_factored
    simp_all only [_root_.mul_eq_zero]

  have h_no_rational : ¬(3 * a + 16 = 0) := by
    clear * - h_options
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    simp_all only [true_or]
    (omega)

  have h_a_val : a = 5 := by
    clear * - h_options h_no_rational
    simp_all only [false_or]
    (nlinarith)

  have h_b_val : b = 2 := by
    clear * - h_prod_int h_a_val
    subst h_a_val
    (nlinarith)

  have h_target : a * b + b = 12 := by
    clear * - h_prod_int h_b_val h_a_val
    subst h_a_val h_b_val
    simp_all only [Int.reduceMul, Int.reduceAdd]

  exact h_target