import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12b_2020_p2 :
    (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) =
      1 := by
  have h_diff1 : (100 ^ 2 - 7 ^ 2 : ℝ) = (100 - 7 : ℝ) * (100 + 7 : ℝ) := by
    clear * -
    (linarith)

  have h_diff2 : (70 ^ 2 - 11 ^ 2 : ℝ) = (70 - 11 : ℝ) * (70 + 11 : ℝ) := by
    clear * -
    (linarith)

  have h_frac1 : (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) = ((100 - 7 : ℝ) * (100 + 7 : ℝ)) / ((70 - 11 : ℝ) * (70 + 11 : ℝ)) := by
    clear * - h_diff1 h_diff2
    simp_all only

  have h_frac2 : ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = ((70 - 11 : ℝ) * (70 + 11 : ℝ)) / ((100 - 7 : ℝ) * (100 + 7 : ℝ)) := by
    clear * -
    simp_all only

  have h_combined : (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) =
    (((100 - 7 : ℝ) * (100 + 7 : ℝ)) / ((70 - 11 : ℝ) * (70 + 11 : ℝ))) * (((70 - 11 : ℝ) * (70 + 11 : ℝ)) / ((100 - 7 : ℝ) * (100 + 7 : ℝ))) := by
    clear * - h_frac1 h_frac2
    simp_all only

  have h_num_cancel : ((100 - 7 : ℝ) * (100 + 7 : ℝ)) / ((100 - 7 : ℝ) * (100 + 7 : ℝ)) = (1 : ℝ) := by
    clear * -
    (linarith)

  have h_den_cancel : ((70 - 11 : ℝ) * (70 + 11 : ℝ)) / ((70 - 11 : ℝ) * (70 + 11 : ℝ)) = (1 : ℝ) := by
    clear * -
    (linarith)

  have h_product : (((100 - 7 : ℝ) * (100 + 7 : ℝ)) / ((70 - 11 : ℝ) * (70 + 11 : ℝ))) * (((70 - 11 : ℝ) * (70 + 11 : ℝ)) / ((100 - 7 : ℝ) * (100 + 7 : ℝ))) = (1 : ℝ) := by
    clear * - h_num_cancel h_den_cancel
    (linarith)

  have h_result : (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = (1 : ℝ) := by
    clear * - h_combined h_product
    simp_all only

  exact h_result
