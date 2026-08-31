import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have hx : 0 < x := by
    clear * - h₀
    (ring)
    (linarith)

  have hy : 0 < y := by
    clear * - h₀
    (linarith)

  have hz : 0 < z := by
    clear * - h₀
    (ring)
    (linarith)

  let a := x + y

  let b := y + z

  let c := z + x

  have ha_pos : 0 < a := by
    clear * - hx hy
    simp_all only [a]
    (linarith)

  have hb_pos : 0 < b := by
    clear * - hy hz
    simp only [b] at *
    (linarith)

  have hc_pos : 0 < c := by
    clear * - hz hx
    simp_all only [c]
    (linarith)

  have h_sum_relation : a + b + c = (2:ℝ) * (x + y + z) := by
    clear * -
    (linarith)

  have h_target_rhs : (9:ℝ) / (x + y + z) = (18:ℝ) / (a + b + c) := by
    clear * - h_sum_relation ha_pos hb_pos hc_pos
    (grind only [one_div])

  have h_lhs_subst : (2:ℝ) / (x + y) + (2:ℝ) / (y + z) + (2:ℝ) / (z + x) = (2:ℝ) / a + (2:ℝ) / b + (2:ℝ) / c := by
    clear * -
    (linarith)

  have h_diff_factorization :
      ((2:ℝ) / a + (2:ℝ) / b + (2:ℝ) / c) - (18:ℝ) / (a + b + c) =
      (2:ℝ) * (((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) - (9:ℝ) / (a + b + c)) := by
    clear * -
    (grind only [div_div])

  have h_common_denominator :
      ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) - (9:ℝ) / (a + b + c) =
      ((a + b + c) * ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) - (9:ℝ)) / (a + b + c) := by
    clear * - ha_pos hb_pos hc_pos
    (grind only [mul_div])

  have h_expansion :
      (a + b + c) * ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) =
      (3:ℝ) + a / b + b / a + b / c + c / b + c / a + a / c := by
    clear * - ha_pos hb_pos hc_pos
    (grind only [mul_div_assoc])

  have h_ab_ge_two : a / b + b / a ≥ (2:ℝ) := by
    clear * - ha_pos hb_pos
    field_simp [ha_pos, hb_pos, add_comm]
    nlinarith [sq_nonneg (b - a), mul_nonneg ha_pos.le hb_pos.le]

  have h_bc_ge_two : b / c + c / b ≥ (2:ℝ) := by
    clear * - hb_pos hc_pos
    field_simp [hb_pos, hc_pos] at *
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]

  have h_ca_ge_two : c / a + a / c ≥ (2:ℝ) := by
    clear * - hc_pos ha_pos
    field_simp [sq]
    nlinarith [sq_nonneg (a - c), mul_pos ha_pos hc_pos]

  have h_product_ge_nine :
      (a + b + c) * ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) ≥ (9:ℝ) := by
    clear * - h_expansion h_ab_ge_two h_bc_ge_two h_ca_ge_two
    simp_all only [one_div, ge_iff_le, a, b, c]
    (linarith)

  have h_num_div_denom_nonneg :
      ((a + b + c) * ((1:ℝ) / a + (1:ℝ) / b + (1:ℝ) / c) - (9:ℝ)) / (a + b + c) ≥ 0 := by
    clear * - h_product_ge_nine ha_pos hb_pos hc_pos
    simp_all only [one_div, ge_iff_le, a, b, c]
    (bound )

  have h_main_diff_nonneg :
      ((2:ℝ) / a + (2:ℝ) / b + (2:ℝ) / c) - (18:ℝ) / (a + b + c) ≥ 0 := by
    clear * - h_diff_factorization h_common_denominator h_num_div_denom_nonneg
    simp_all only [one_div, ge_iff_le, ofNat_pos, mul_nonneg_iff_of_pos_left, a, b, c]

  have h_final_statement :
      (9:ℝ) / (x + y + z) ≤ (2:ℝ) / (x + y) + (2:ℝ) / (y + z) + (2:ℝ) / (z + x) := by
    clear * - h_target_rhs h_lhs_subst h_main_diff_nonneg
    simp_all only [ge_iff_le, sub_nonneg, a, b, c]

  exact h_final_statement
