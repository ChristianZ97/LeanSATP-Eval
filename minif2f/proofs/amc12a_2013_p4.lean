import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12a_2013_p4 : (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by
  have h_pow_split : (2 : ℝ) ^ 2014 = (2 : ℝ) ^ 2012 * (2 : ℝ) ^ 2 := by
    clear * -
    (ring)
    (field_simp)
    (linarith)

  have h_num_expand : (2 : ℝ) ^ 2014 + (2 : ℝ) ^ 2012 = (2 : ℝ) ^ 2012 * (2 : ℝ) ^ 2 + (2 : ℝ) ^ 2012 * (1 : ℝ) := by
    clear * - h_pow_split
    simp_all only [mul_one]

  have h_den_expand : (2 : ℝ) ^ 2014 - (2 : ℝ) ^ 2012 = (2 : ℝ) ^ 2012 * (2 : ℝ) ^ 2 - (2 : ℝ) ^ 2012 * (1 : ℝ) := by
    clear * - h_pow_split
    simp_all only [mul_one]

  have h_num_factor : (2 : ℝ) ^ 2014 + (2 : ℝ) ^ 2012 = (2 : ℝ) ^ 2012 * ((2 : ℝ) ^ 2 + 1) := by
    clear * - h_num_expand
    simp_all only [mul_one, add_left_inj]
    (linarith)

  have h_den_factor : (2 : ℝ) ^ 2014 - (2 : ℝ) ^ 2012 = (2 : ℝ) ^ 2012 * ((2 : ℝ) ^ 2 - 1) := by
    clear * - h_den_expand
    simp_all only [mul_one, sub_left_inj]
    (linarith)

  have h_cancel_common : ((2 : ℝ) ^ 2014 + (2 : ℝ) ^ 2012) / ((2 : ℝ) ^ 2014 - (2 : ℝ) ^ 2012) = ((2 : ℝ) ^ 2 + 1) / ((2 : ℝ) ^ 2 - 1) := by
    clear * - h_num_factor h_den_factor
    simp_all only
    (grind only [eq_div_iff_mul_eq])

  have h_sq_val : (2 : ℝ) ^ 2 = (4 : ℝ) := by
    clear * -
    (linarith)

  have h_sub_val : ((2 : ℝ) ^ 2 + 1) / ((2 : ℝ) ^ 2 - 1) = ((4 : ℝ) + (1 : ℝ)) / ((4 : ℝ) - (1 : ℝ)) := by
    clear * - h_sq_val
    simp_all only

  have h_calc : ((4 : ℝ) + (1 : ℝ)) / ((4 : ℝ) - (1 : ℝ)) = (5 : ℝ) / (3 : ℝ) := by
    clear * -
    (linarith)

  have h_final : ((2 : ℝ) ^ 2014 + (2 : ℝ) ^ 2012) / ((2 : ℝ) ^ 2014 - (2 : ℝ) ^ 2012) = (5 : ℝ) / (3 : ℝ) := by
    clear * - h_cancel_common h_sub_val h_calc
    simp_all only

  exact h_final
