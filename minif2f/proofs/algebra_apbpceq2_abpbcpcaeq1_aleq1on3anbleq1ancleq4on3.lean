import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
  0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have h_sum_sq : a ^ 2 + b ^ 2 + c ^ 2 = 2 := by
    clear * - h₁ h₂
    (nlinarith)

  have h_bc_sum : b + c = 2 - a := by
    clear * - h₁
    (nlinarith)

  have h_bc_sq : b ^ 2 + c ^ 2 = 2 - a ^ 2 := by
    clear * - h_sum_sq
    (nlinarith)

  have h_cauchy : (b + c) ^ 2 ≤ 2 * (b ^ 2 + c ^ 2) := by
    clear * -
    linarith [sq_nonneg (b - c)]

  have h_quad_ineq : (2 - a) ^ 2 ≤ 2 * (2 - a ^ 2) := by
    clear * - h_bc_sum h_bc_sq h_cauchy
    simp_all only

  have h_a_quad : 3 * a ^ 2 - 4 * a ≤ 0 := by
    clear * - h_quad_ineq
    simp_all only [tsub_le_iff_right, zero_add]
    (nlinarith)

  have h_a_range_initial : 0 ≤ a ∧ a ≤ 4 / 3 := by
    clear * - h_a_quad
    simp_all only [tsub_le_iff_right, zero_add]
    apply And.intro
    · (nlinarith)
    · (nlinarith)

  simp_all only [tsub_le_iff_right, zero_add, one_div, true_and]
  constructor <;> norm_num
  · simp_all only [one_div]
    norm_num at * <;> nlinarith

  · simp_all only [one_div]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith