import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem algebra_bleqa_apbon2msqrtableqambsqon8b (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : b ≤ a) :
    (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  have ha_pos : 0 < a := by
    clear * - h₀
    (ring)
    (linarith)

  have hb_pos : 0 < b := by
    clear * - h₀
    (ring)
    (linarith)

  have h_step2 : Real.sqrt b ≤ Real.sqrt a := by
    clear * - ha_pos hb_pos h₁
    (bound )

  have h_step3 : (2 : ℝ) * Real.sqrt b ≤ Real.sqrt a + Real.sqrt b := by
    clear * - h_step2 hb_pos
    (linarith)

  have h_step4 : (4 : ℝ) * b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    clear * - h_step3 ha_pos hb_pos
    nlinarith [Real.sq_sqrt ha_pos.le, Real.sq_sqrt hb_pos.le, sq_nonneg (√a - √b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]

  have h_denom_pos : 0 < (8 : ℝ) * b := by
    clear * - hb_pos
    (linarith)

  have h_factor_nonneg : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := by
    clear * - ha_pos hb_pos
    (nlinarith)

  have h_step5 : ((4 : ℝ) * b * (Real.sqrt a - Real.sqrt b) ^ 2) / ((8 : ℝ) * b) ≤ ((Real.sqrt a + Real.sqrt b) ^ 2 * (Real.sqrt a - Real.sqrt b) ^ 2) / ((8 : ℝ) * b) := by
    clear * - h_step4 h_factor_nonneg h_denom_pos
    simp only [ofNat_pos, mul_pos_iff_of_pos_left] at *
    (bound )

  have h_step6_lhs : ((4 : ℝ) * b * (Real.sqrt a - Real.sqrt b) ^ 2) / ((8 : ℝ) * b) = (1 : ℝ) / 2 * (Real.sqrt a - Real.sqrt b) ^ 2 := by
    clear * - hb_pos
    (bound )
    (grind only [Real.div_sqrt])

  have h_step6_rhs : ((Real.sqrt a + Real.sqrt b) ^ 2 * (Real.sqrt a - Real.sqrt b) ^ 2) = (((Real.sqrt a + Real.sqrt b) * (Real.sqrt a - Real.sqrt b))) ^ 2 := by
    clear * - ha_pos hb_pos
    (linarith)

  have h_step6 : (1 : ℝ) / 2 * (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (((Real.sqrt a + Real.sqrt b) * (Real.sqrt a - Real.sqrt b))) ^ 2 / ((8 : ℝ) * b) := by
    clear * - h_step5 h_step6_lhs h_step6_rhs
    simp_all only [one_div]

  have h_diff_sq : (Real.sqrt a + Real.sqrt b) * (Real.sqrt a - Real.sqrt b) = a - b := by
    clear * - ha_pos hb_pos
    nlinarith [sq_sqrt ha_pos.le, sq_sqrt hb_pos.le, mul_self_nonneg (Real.sqrt a - Real.sqrt b)]

  have h_step7 : (1 : ℝ) / 2 * (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) ^ 2 / ((8 : ℝ) * b) := by
    clear * - h_step6 h_diff_sq
    simp_all only [one_div]

  have h_expand_sq : (Real.sqrt a - Real.sqrt b) ^ 2 = a - 2 * Real.sqrt (a * b) + b := by
    clear * - ha_pos hb_pos
    (bound )
    (simp_all)
    (grind only [Real.mul_self_sqrt])

  have h_step8 : (1 : ℝ) / 2 * (a - 2 * Real.sqrt (a * b) + b) ≤ (a - b) ^ 2 / ((8 : ℝ) * b) := by
    clear * - h_step7 h_expand_sq
    simp_all only [one_div]

  have h_distribute : (1 : ℝ) / 2 * (a - 2 * Real.sqrt (a * b) + b) = a / 2 - Real.sqrt (a * b) + b / 2 := by
    clear * - ha_pos hb_pos
    (linarith)

  have h_step9 : a / 2 - Real.sqrt (a * b) + b / 2 ≤ (a - b) ^ 2 / ((8 : ℝ) * b) := by
    clear * - h_step8 h_distribute
    simp_all only [one_div]

  have h_regroup : a / 2 - Real.sqrt (a * b) + b / 2 = (a + b) / 2 - Real.sqrt (a * b) := by
    clear * - ha_pos hb_pos
    (linarith)

  have h_step10 : (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / ((8 : ℝ) * b) := by
    clear * - h_step9 h_regroup
    simp_all only [tsub_le_iff_right]

  exact h_step10
