import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem imo_1983_p6 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  set x := (b + c - a) / 2 with hx_def
  set y := (a + c - b) / 2 with hy_def
  set z := (a + b - c) / 2 with hz_def

  have hx_pos : 0 < x := by
    linarith [h₃]

  have hy_pos : 0 < y := by
    linarith [h₂]

  have hz_pos : 0 < z := by
    linarith [h₁]

  have ha_eq : a = y + z := by
    linarith [hy_def, hz_def]

  have hb_eq : b = z + x := by
    linarith [hz_def, hx_def]

  have hc_eq : c = x + y := by
    linarith [hx_def, hy_def]

  have h_main_goal : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
    rw [ha_eq, hb_eq, hc_eq]

    have h_identity :
      (y + z) ^ 2 * (z + x) * ((y + z) - (z + x)) +
      (z + x) ^ 2 * (x + y) * ((z + x) - (x + y)) +
      (x + y) ^ 2 * (y + z) * ((x + y) - (y + z)) =
      2 * x * y * z * ((x ^ 2 / y + y ^ 2 / z + z ^ 2 / x) - (x + y + z)) := by
      have h_field : y ≠ 0 := by linarith
      have h_field_y : z ≠ 0 := by linarith
      have h_field_z : x ≠ 0 := by linarith
      field_simp [h_field, h_field_y, h_field_z]
      ring_nf

    rw [h_identity]

    have h_pos_factor : 0 ≤ 2 * x * y * z := by
      have h_prod_pos : 0 < x * y * z := by positivity
      linarith

    have h_diff_form :
      (x ^ 2 / y + y ^ 2 / z + z ^ 2 / x) - (x + y + z) =
      (x - y) ^ 2 / y + (y - z) ^ 2 / z + (z - x) ^ 2 / x := by
      have h_y_ne_zero : y ≠ 0 := by linarith
      have h_z_ne_zero : z ≠ 0 := by linarith
      have h_x_ne_zero : x ≠ 0 := by linarith
      field_simp [h_y_ne_zero, h_z_ne_zero, h_x_ne_zero]
      ring_nf

    rw [h_diff_form]

    have h_terms_nonneg : 0 ≤ (x - y) ^ 2 / y + (y - z) ^ 2 / z + (z - x) ^ 2 / x := by
      have h_sq1 : 0 ≤ (x - y) ^ 2 := sq_nonneg _
      have h_sq2 : 0 ≤ (y - z) ^ 2 := sq_nonneg _
      have h_sq3 : 0 ≤ (z - x) ^ 2 := sq_nonneg _
      have h_div1 : 0 ≤ (x - y) ^ 2 / y := by
        apply div_nonneg h_sq1
        linarith [hy_pos]

      have h_div2 : 0 ≤ (y - z) ^ 2 / z := by
        apply div_nonneg h_sq2
        linarith [hz_pos]

      have h_div3 : 0 ≤ (z - x) ^ 2 / x := by
        apply div_nonneg h_sq3
        linarith [hx_pos]

      linarith [h_div1, h_div2, h_div3]

    have h_final_mult : 0 ≤ 2 * x * y * z * ((x - y) ^ 2 / y + (y - z) ^ 2 / z + (z - x) ^ 2 / x) := by
      apply mul_nonneg h_pos_factor h_terms_nonneg

    exact h_final_mult

  exact h_main_goal
