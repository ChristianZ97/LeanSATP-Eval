import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  let x := (b + c - a) / (2 : ℝ)
  let y := (c + a - b) / (2 : ℝ)
  let z := (a + b - c) / (2 : ℝ)

  have hx_pos : 0 < x := by
    clear * - h₃
    simp only [x] at *
    (linarith)

  have hy_pos : 0 < y := by
    clear * - h₂
    simp only [y] at *
    (linarith)

  have hz_pos : 0 < z := by
    clear * - h₁
    simp only [z] at *
    (linarith)

  have ha_eq : a = y + z := by
    clear * - hx_pos hy_pos hz_pos
    (grind only [mul_div_cancel_left])

  have hb_eq : b = x + z := by
    clear * - hx_pos hy_pos hz_pos
    (grind only [mul_div_cancel_left])

  have hc_eq : c = x + y := by
    clear * - hx_pos hy_pos hz_pos
    (grind only [mul_div_cancel_left])

  have t1_exp : b + c - a = 2 * x := by
    clear * - ha_eq hb_eq hc_eq
    (linarith)

  have t1_subst : a ^ 2 * (b + c - a) = (y + z) ^ 2 * (2 * x) := by
    clear * - ha_eq t1_exp
    (grind only [sum_eight_sq_mul_sum_eight_sq])

  have t2_exp : c + a - b = 2 * y := by
    clear * - ha_eq hb_eq hc_eq
    (linarith)

  have t2_subst : b ^ 2 * (c + a - b) = (x + z) ^ 2 * (2 * y) := by
    clear * - hb_eq t2_exp
    (grind only [sum_eight_sq_mul_sum_eight_sq])

  have t3_exp : a + b - c = 2 * z := by
    clear * - ha_eq hb_eq hc_eq
    (linarith)

  have t3_subst : c ^ 2 * (a + b - c) = (x + y) ^ 2 * (2 * z) := by
    clear * - hc_eq t3_exp
    (grind only [sum_eight_sq_mul_sum_eight_sq])

  have lhs_sum : a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) =
      (y + z) ^ 2 * (2 * x) + (x + z) ^ 2 * (2 * y) + (x + y) ^ 2 * (2 * z) := by
    clear * - t1_subst t2_subst t3_subst
    (linarith)

  have lhs_factor : (y + z) ^ 2 * (2 * x) + (x + z) ^ 2 * (2 * y) + (x + y) ^ 2 * (2 * z) =
      2 * (x * (y + z) ^ 2 + y * (x + z) ^ 2 + z * (x + y) ^ 2) := by
    clear * - lhs_sum
    (linarith)

  have rhs_subst : 3 * a * b * c = 3 * (y + z) * (x + z) * (x + y) := by
    clear * - ha_eq hb_eq hc_eq
    (grind only [mul_div_assoc])

  have step_12_1 : x * (y + z) ^ 2 = x * y ^ 2 + 2 * x * y * z + x * z ^ 2 := by
    clear * -
    (linarith)

  have step_12_2 : y * (x + z) ^ 2 = y * x ^ 2 + 2 * x * y * z + y * z ^ 2 := by
    clear * -
    (linarith)

  have step_12_3 : z * (x + y) ^ 2 = z * x ^ 2 + 2 * x * y * z + z * y ^ 2 := by
    clear * -
    (linarith)

  have sum_parts : x * (y + z) ^ 2 + y * (x + z) ^ 2 + z * (x + y) ^ 2 =
      (x * y ^ 2 + x * z ^ 2 + y * x ^ 2 + y * z ^ 2 + z * x ^ 2 + z * y ^ 2) + 6 * x * y * z := by
    clear * - step_12_1 step_12_2 step_12_3
    simp_all only [x, y, z]
    (linarith)

  have lhs_final : 2 * (x * (y + z) ^ 2 + y * (x + z) ^ 2 + z * (x + y) ^ 2) =
      2 * (x * y ^ 2 + x * z ^ 2 + y * x ^ 2 + y * z ^ 2 + z * x ^ 2 + z * y ^ 2) + 12 * x * y * z := by
    clear * - sum_parts
    (linarith)

  have prod_identity : (x + y) * (y + z) * (z + x) =
      (x * y ^ 2 + x * z ^ 2 + y * x ^ 2 + y * z ^ 2 + z * x ^ 2 + z * y ^ 2) + 2 * x * y * z := by
    clear * -
    (linarith)

  have rhs_final : 3 * (y + z) * (x + z) * (x + y) =
      3 * (x * y ^ 2 + x * z ^ 2 + y * x ^ 2 + y * z ^ 2 + z * x ^ 2 + z * y ^ 2) + 6 * x * y * z := by
    clear * - prod_identity
    (linarith)

  have am_gm_step : x * y ^ 2 + x * z ^ 2 + y * x ^ 2 + y * z ^ 2 + z * x ^ 2 + z * y ^ 2 ≥ 6 * x * y * z := by
    clear * - hx_pos hy_pos hz_pos
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

  have inequality_proof :
      2 * (x * y ^ 2 + x * z ^ 2 + y * x ^ 2 + y * z ^ 2 + z * x ^ 2 + z * y ^ 2) + 12 * x * y * z ≤
      3 * (x * y ^ 2 + x * z ^ 2 + y * x ^ 2 + y * z ^ 2 + z * x ^ 2 + z * y ^ 2) + 6 * x * y * z := by
    clear * - am_gm_step
    simp only [ge_iff_le, x, y, z] at *
    (linarith)

  exact by
    clear * - lhs_final rhs_final inequality_proof
    simp only [ge_iff_le, x, y, z] at *
    (linarith)
