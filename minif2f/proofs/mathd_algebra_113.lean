import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have h1 : x ^ 2 - (14 : ℝ) * x + (3 : ℝ) = x ^ 2 - (14 : ℝ) * x + (49 : ℝ) - (49 : ℝ) + (3 : ℝ) := by
    clear * -
    (linarith)

  have h2 : x ^ 2 - (14 : ℝ) * x + (49 : ℝ) = (x - (7 : ℝ)) ^ 2 := by
    clear * -
    (linarith)

  have h3 : -(49 : ℝ) + (3 : ℝ) = -(46 : ℝ) := by
    clear * -
    (linarith)

  have h4 : x ^ 2 - (14 : ℝ) * x + (3 : ℝ) = (x - (7 : ℝ)) ^ 2 - (46 : ℝ) := by
    clear * - h1 h2 h3
    (linarith)

  have h5 : (x - (7 : ℝ)) ^ 2 ≥ (0 : ℝ) := by
    clear * -
    exact sq_nonneg (x - 7)

  have h6 : (x - (7 : ℝ)) ^ 2 - (46 : ℝ) ≥ -(46 : ℝ) := by
    clear * - h5
    simp_all only [ge_iff_le, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]

  have h7 : (7 : ℝ) ^ 2 - (14 : ℝ) * (7 : ℝ) + (3 : ℝ) = (49 : ℝ) - (98 : ℝ) + (3 : ℝ) := by
    clear * -
    simp_all only [add_left_inj]
    (linarith)

  have h8 : (49 : ℝ) - (98 : ℝ) + (3 : ℝ) = -(49 : ℝ) + (3 : ℝ) := by
    clear * -
    (linarith)

  have h9 : -(49 : ℝ) + (3 : ℝ) = -(46 : ℝ) := by
    clear * -
    (linarith)

  have h_rhs_val : (7 : ℝ) ^ 2 - (14 : ℝ) * (7 : ℝ) + (3 : ℝ) = -(46 : ℝ) := by
    clear * - h7 h8 h9
    (linarith)

  have h10 : x ^ 2 - (14 : ℝ) * x + (3 : ℝ) ≥ (7 : ℝ) ^ 2 - (14 : ℝ) * (7 : ℝ) + (3 : ℝ) := by
    clear * - h4 h6 h_rhs_val
    simp_all only [ge_iff_le, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]

  exact h10
