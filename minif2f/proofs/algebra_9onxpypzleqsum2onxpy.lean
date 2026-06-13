import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  let a := x + y
  let b := y + z
  let c := z + x

  have ha_pos : 0 < a := by
    clear * - h₀
    simp_all only [a]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    (nlinarith)

  have hb_pos : 0 < b := by
    clear * - h₀
    simp_all only [b]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    (nlinarith)

  have hc_pos : 0 < c := by
    clear * - h₀
    simp_all only [c]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    (nlinarith)

  have h_sum_relation : a + b + c = 2 * (x + y + z) := by
    clear * -
    simp_all only [a, b, c]
    (nlinarith)

  have h_xyz_expr : x + y + z = (a + b + c) / 2 := by
    clear * - h_sum_relation
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, a, b, c]

  have h_lhs_val : (9:ℝ) / (x + y + z) = (18:ℝ) / (a + b + c) := by
    clear * - h_xyz_expr
    simp_all only [a, b, c]
    (field_simp)
    (nlinarith)

  have h_rhs_val : (2:ℝ) / (x + y) + (2:ℝ) / (y + z) + (2:ℝ) / (z + x) = (2:ℝ) / a + (2:ℝ) / b + (2:ℝ) / c := by
    clear * -
    simp_all only [a, b, c]

  have h_rhs_factored : (2:ℝ) / a + (2:ℝ) / b + (2:ℝ) / c = (2:ℝ) * ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) := by
    clear * - ha_pos hb_pos hc_pos
    simp_all only [one_div, a, b, c]
    (field_simp)
    (nlinarith)

  have h_prod_expansion : ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) * (a + b + c) = (3:ℝ) + (a / b + b / a) + (b / c + c / b) + (c / a + a / c) := by
    clear * - ha_pos hb_pos hc_pos
    simp_all only [one_div, a, b, c]
    (field_simp)
    (nlinarith)

  have h_pair_ab : a / b + b / a = ((a - b) : ℝ) ^ 2 / (a * b) + (2:ℝ) := by
    clear * - ha_pos hb_pos
    simp_all only [a, b]
    (field_simp)
    (nlinarith)

  have h_pair_bc : b / c + c / b = ((b - c) : ℝ) ^ 2 / (b * c) + (2:ℝ) := by
    clear * - hb_pos hc_pos
    simp_all only [b, c]
    (field_simp)
    (nlinarith)

  have h_pair_ca : c / a + a / c = ((c - a) : ℝ) ^ 2 / (c * a) + (2:ℝ) := by
    clear * - hc_pos ha_pos
    simp_all only [a, c]
    (field_simp)
    (nlinarith)

  have h_prod_value : ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) * (a + b + c) = (9:ℝ) + ((a - b) : ℝ) ^ 2 / (a * b) + ((b - c) : ℝ) ^ 2 / (b * c) + ((c - a) : ℝ) ^ 2 / (c * a) := by
    clear * - h_prod_expansion h_pair_ab h_pair_bc h_pair_ca
    simp_all [a, b, c]
    (nlinarith)

  have h_squares_nonneg : ((a - b) : ℝ) ^ 2 / (a * b) + ((b - c) : ℝ) ^ 2 / (b * c) + ((c - a) : ℝ) ^ 2 / (c * a) ≥ (0:ℝ) := by
    clear * - ha_pos hb_pos hc_pos
    simp_all only [ge_iff_le, a, b, c]
    (field_simp)
    (bound )

  have h_inequality_product : ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) * (a + b + c) ≥ (9:ℝ) := by
    clear * - h_prod_value h_squares_nonneg
    simp_all only [one_div, ge_iff_le, a, b, c]
    (nlinarith)

  have h_reciprocal_bound : ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) ≥ (9:ℝ) / (a + b + c) := by
    clear * - h_inequality_product ha_pos hb_pos hc_pos
    simp_all only [one_div, ge_iff_le, a, b, c]
    exact (div_le_iff (by positivity)).mpr h_inequality_product

  have h_rich_bound : (2:ℝ) * ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) ≥ (18:ℝ) / (a + b + c) := by
    clear * - h_reciprocal_bound
    simp_all only [one_div, ge_iff_le, a, b, c]
    rw [mul_comm]
    ring_nf at h_reciprocal_bound ⊢ <;> linarith

  have h_goal : (9:ℝ) / (x + y + z) ≤ (2:ℝ) / (x + y) + (2:ℝ) / (y + z) + (2:ℝ) / (z + x) := by
    clear * - h_lhs_val h_rhs_val h_rhs_factored h_rich_bound
    simp_all only [one_div, ge_iff_le, a, b, c]

  exact h_goal