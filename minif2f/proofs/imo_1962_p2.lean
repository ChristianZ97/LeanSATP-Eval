import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem imo_1962_p2 (x : ℝ) (h₀ : 0 ≤ 3 - x) (h₁ : 0 ≤ x + 1)
    (h₂ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)) : -1 ≤ x ∧ x < 1 - Real.sqrt 31 / 8 := by
  have h_step_1 : Real.sqrt (3 - x) > Real.sqrt (x + 1) + (1:ℝ) / 2 := by
    clear * - h₂
    simp_all only [one_div, gt_iff_lt]
    (nlinarith)

  have h_step_2 : 3 - x > (Real.sqrt (x + 1) + (1:ℝ) / 2) ^ 2 := by
    clear * - h_step_1 h₀ h₁
    nlinarith [Real.sq_sqrt (show 0 ≤ 3 - x by linarith), Real.sqrt_nonneg (x + 1), Real.sq_sqrt (show 0 ≤ x + 1 by linarith)]

  have h_step_3 : 3 - x > (x + 1) + Real.sqrt (x + 1) + ((1:ℝ) / 4) := by
    clear * - h_step_2
    erw [add_sq] at h_step_2
    simp only [sq, one_div] at h_step_2
    norm_num [mul_add] at *
    by_contra res
    on_goal 1 => revert h_step_2
    intro hp
    refine' res _
    nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt (show 0 ≤ (x + 1) by nlinarith [Real.sqrt_nonneg (x + 1)])]

  have h_step_4 : Real.sqrt (x + 1) < ((7:ℝ) / 4) - 2 * x := by
    clear * - h_step_3
    (nlinarith)

  have h_step_5 : ((7:ℝ) / 4) - 2 * x ≥ 0 := by
    clear * - h_step_4 h₁
    linarith [Real.sqrt_nonneg (x + 1), h₁]

  have h_step_6 : x + 1 < (((7:ℝ) / 4) - 2 * x) ^ 2 := by
    clear * - h_step_4 h_step_5
    nth_rewrite 1 [← not_le]
    intro b
    refine h_step_4.not_le (le_of_sub_nonneg ?_)
    nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt (by nlinarith : 0 ≤ x + 1)]

  have h_step_7 : 64 * x ^ 2 - 128 * x + 33 > 0 := by
    clear * - h_step_6
    simp only [gt_iff_lt] at *
    (nlinarith)

  have h_step_8 : x < 1 - Real.sqrt 31 / 8 ∨ x > 1 + Real.sqrt 31 / 8 := by
    clear * - h_step_7
    by_cases hx : x < 1 - √31 / 8
    · exact Or.inl hx
    · exact (or_iff_not_imp_left.2 fun h => by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 31)])

  have h_step_9 : x < 1 - Real.sqrt 31 / 8 := by
    clear * - h_step_8 h_step_5
    simp only [ge_iff_le, sub_nonneg, gt_iff_lt] at *
    (grind only [mul_lt_mul_left])

  have h_step_10 : -1 ≤ x := by
    clear * - h₁
    (linarith)

  exact ⟨h_step_10, h_step_9⟩
