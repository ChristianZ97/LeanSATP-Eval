import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

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
    congr 1
    norm_num [divInt_eq_div, Int.cast_ofNat]

  have h_step_2 : f ((25 : ℚ) * ((1 : ℚ) / (11 : ℚ))) = f (25 : ℚ) + f ((1 : ℚ) / (11 : ℚ)) := by
    clear * - h₀ h_pos_25
    simp_all only [gt_iff_lt, ofNat_pos, one_div, inv_pos]

  have h_step_3 : f (1 : ℚ) = f ((11 : ℚ) * ((1 : ℚ) / (11 : ℚ))) := by
    clear * - h_pos_11
    simp_all only [gt_iff_lt, ofNat_pos, one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀]

  have h_step_4 : f ((11 : ℚ) * ((1 : ℚ) / (11 : ℚ))) = f (11 : ℚ) + f ((1 : ℚ) / (11 : ℚ)) := by
    clear * - h₀ h_pos_11
    simp_all only [gt_iff_lt, ofNat_pos, one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀]
    (grind only [one_div])

  have h_step_5 : f (1 : ℚ) = 0 := by
    clear * - h₀ h_pos_one
    have := h₀ 1 h_pos_one 1 h_pos_one <;> simp_all

  have h_step_6 : f (11 : ℚ) + f ((1 : ℚ) / (11 : ℚ)) = 0 := by
    clear * - h_step_3 h_step_4 h_step_5
    simp_all only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀]

  have h_step_7 : f ((1 : ℚ) / (11 : ℚ)) = -(f (11 : ℚ)) := by
    clear * - h_step_6
    simp_all only [one_div]
    (linarith)

  have h_step_8 : f (25 /. 11) = f (25 : ℚ) - f (11 : ℚ) := by
    clear * - h_step_1 h_step_2 h_step_7
    (linarith)

  have h_step_9 : f (25 : ℚ) = f ((5 : ℚ) * (5 : ℚ)) := by
    clear * - h_pos_5
    simp only [gt_iff_lt, ofNat_pos] at *
    (ring)

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
    (linarith)

  have h_step_14 : f (11 : ℚ) = (11 : ℝ) := by
    clear * - h₁ h_prime_11
    (bound )

  have h_step_15 : f (25 /. 11) = (10 : ℝ) - (11 : ℝ) := by
    clear * - h_step_8 h_step_13 h_step_14
    simp_all only

  have h_step_16 : f (25 /. 11) = (-1 : ℝ) := by
    clear * - h_step_15
    simp_all only
    (ring)

  have h_step_17 : f (25 /. 11) < 0 := by
    clear * - h_step_16
    (ring)
    (linarith)

  exact h_step_17
