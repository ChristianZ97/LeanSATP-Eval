import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =

      2 := by
  have : (80 : ℝ) = 2 ^ 4 * 5 := by norm_cast
  field_simp [this, show (40 : ℝ) = 2 * 20 by norm_num, show (160 : ℝ) = 2 * 80 by norm_num] <;> ring
  aesop  (add simp [Real.log_mul])
  simp [show (40 : ℝ) = 2 ^ 3 * 5 by norm_num, show (160 : ℝ) = 2 ^ 5 * 5 by norm_num, show (20 : ℝ) = 2 ^ 2 * 5 by norm_num]
  simp [Real.log_mul, Real.log_pow] <;> ring
