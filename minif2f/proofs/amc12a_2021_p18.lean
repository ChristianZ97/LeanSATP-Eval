import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f (25 /. 11) < 0 := by
  have h_pos_25 : (25 : ℚ) > 0 := by norm_num
  have h_pos_11 : (11 : ℚ) > 0 := by norm_num
  have h_pos_5 : (5 : ℚ) > 0 := by norm_num
  have h_pos_one : (1 : ℚ) > 0 := by norm_num

  have h_prime_5 : Nat.Prime 5 := by norm_num
  have h_prime_11 : Nat.Prime 11 := by norm_num

  have h_step_1 : f (25 /. 11) = f ((25 : ℚ) * ((1 : ℚ) / (11 : ℚ))) := by
    clear * - h_pos_25 h_pos_11
    simp_all only [gt_iff_lt, ofNat_pos, one_div]
    (field_simp)
    (norm_cast at *)
    simp_all only [NNRat.cast_divNat, Nat.cast_ofNat]

  have h_step_2 : f ((25 : ℚ) * ((1 : ℚ) / (11 : ℚ))) = f (25 : ℚ) + f ((1 : ℚ) / (11 : ℚ)) := by
    clear * - h₀ h_pos_25
    simp_all only [gt_iff_lt, ofNat_pos, one_div, inv_pos]

  have h_step_3 : f (1 : ℚ) = f ((11 : ℚ) * ((1 : ℚ) / (11 : ℚ))) := by
    clear * - h_pos_11
    simp_all only [gt_iff_lt, ofNat_pos, one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀]

  have h_step_4 : f ((11 : ℚ) * ((1 : ℚ) / (11 : ℚ))) = f (11 : ℚ) + f ((1 : ℚ) / (11 : ℚ)) := by
    clear * - h₀ h_pos_11
    simp_all only [gt_iff_lt, ofNat_pos, one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀]
    have t := h₀ (11 : ℚ) (by norm_num) (11⁻¹ : ℚ) (by norm_num)
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀]

  have h_step_5 : f (1 : ℚ) = 0 := by
    clear * - h₀ h_pos_one
    simp_all only [gt_iff_lt, zero_lt_one]
    set c := f 1
    simp_all only [c]
    have hc := h₀ 1
    simp_all only [zero_lt_one, one_mul, self_eq_add_left, forall_const]
    simpa [c] using hc 1 one_pos

  have h_step_6 : f (11 : ℚ) + f ((1 : ℚ) / (11 : ℚ)) = 0 := by
    clear * - h_step_3 h_step_4 h_step_5
    simp_all only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀]

  have h_step_7 : f ((1 : ℚ) / (11 : ℚ)) = -(f (11 : ℚ)) := by
    clear * - h_step_6
    simp_all only [one_div]
    linarith only [h_step_6]

  have h_step_8 : f (25 /. 11) = f (25 : ℚ) - f (11 : ℚ) := by
    clear * - h_step_1 h_step_2 h_step_7
    simp_all only [one_div]
    rfl

  have h_step_9 : f (25 : ℚ) = f ((5 : ℚ) * (5 : ℚ)) := by
    clear * - h_pos_5
    simp_all only [gt_iff_lt, ofNat_pos]
    (norm_num [*] at *)

  have h_step_10 : f ((5 : ℚ) * (5 : ℚ)) = f (5 : ℚ) + f (5 : ℚ) := by
    clear * - h₀ h_pos_5
    simp_all only [gt_iff_lt, ofNat_pos]

  have h_step_11 : f (5 : ℚ) = (5 : ℝ) := by
    clear * - h₁ h_prime_5
    (bound )

  have h_step_12 : f ((5 : ℚ) * (5 : ℚ)) = (5 : ℝ) + (5 : ℝ) := by
    clear * - h_step_10 h_step_11
    simp_all only

  have h_step_13 : f (25 : ℚ) = (10 : ℝ) := by
    clear * - h_step_9 h_step_12
    simp_all only
    (nlinarith)

  have h_step_14 : f (11 : ℚ) = (11 : ℝ) := by
    clear * - h₁ h_prime_11
    (bound )

  have h_step_15 : f (25 /. 11) = (10 : ℝ) - (11 : ℝ) := by
    clear * - h_step_8 h_step_13 h_step_14
    simp_all only

  have h_step_16 : f (25 /. 11) = (-1 : ℝ) := by
    clear * - h_step_15
    simp_all only
    (nlinarith)

  have h_step_17 : f (25 /. 11) < 0 := by
    clear * - h_step_16
    simp_all only [Left.neg_neg_iff, zero_lt_one]

  exact h_step_17