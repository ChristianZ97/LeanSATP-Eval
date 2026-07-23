import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  have h_y_neg : y < 0 := by
    clear * - h₀
    (ring)
    (linarith)

  have h_y_val : y = (-6:ℝ) := by
    clear * - h_y_neg h₁
    cases' abs_cases y with h_pos h_nonpos <;> linarith

  have h_sq_15 : (15:ℝ) ^ 2 = 225 := by
    clear * -
    (linarith)

  have h_dist_sq : (x - (8:ℝ)) ^ 2 + (y - (3:ℝ)) ^ 2 = 225 := by
    clear * - h₂ h_sq_15
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity)] at h₂ <;> linarith

  have h_sub_y : (x - (8:ℝ)) ^ 2 + ((-6:ℝ) - (3:ℝ)) ^ 2 = 225 := by
    clear * - h_dist_sq h_y_val
    subst h_y_val
    simp_all only

  have h_arith_sub : (-6:ℝ) - (3:ℝ) = (-9:ℝ) := by
    clear * -
    (linarith)

  have h_dist_subst : (x - (8:ℝ)) ^ 2 + (-9:ℝ) ^ 2 = 225 := by
    clear * - h_sub_y h_arith_sub
    simp_all only [even_two, Even.neg_pow]

  have h_sq_neg9 : (-9:ℝ) ^ 2 = 81 := by
    clear * -
    simp_all only [even_two, Even.neg_pow]
    (linarith)

  have h_eq_81 : (x - (8:ℝ)) ^ 2 + 81 = 225 := by
    clear * - h_dist_subst h_sq_neg9
    simp_all only [even_two, Even.neg_pow]

  have h_x_diff_sq : (x - (8:ℝ)) ^ 2 = 144 := by
    clear * - h_eq_81
    (linarith)

  have h_x_lt_0 : x < 0 := by
    clear * - h₀
    (ring)
    (linarith)

  have h_x_diff_neg : x - (8:ℝ) < 0 := by
    clear * - h_x_lt_0
    simp only [sub_neg] at *
    (ring)
    (linarith)

  have h_x_diff_val : x - (8:ℝ) = (-12:ℝ) := by
    clear * - h_x_diff_sq h_x_diff_neg
    simp only [sub_neg] at *
    (ring)
    (nlinarith)

  have h_x_val : x = (-4:ℝ) := by
    clear * - h_x_diff_val
    (grind only [div_eq_iff_eq_mul])

  have h_x_sq : x ^ 2 = 16 := by
    clear * - h_x_val
    simp_all only [even_two, Even.neg_pow]
    (linarith)

  have h_y_sq : y ^ 2 = 36 := by
    clear * - h_y_val
    simp_all only [even_two, Even.neg_pow]
    (linarith)

  have h_sum_sq : x ^ 2 + y ^ 2 = 52 := by
    clear * - h_x_sq h_y_sq
    simp_all only
    (linarith)

  have h_n_real : (n : ℝ) = 52 := by
    clear * - h₃ h_sum_sq
    simp_all only [ofNat_nonneg, NNReal.zero_le_coe, sqrt_inj]

  have h_final : n = 52 := by
    clear * - h_n_real
    (ring)
    (bound )

  exact h_final
