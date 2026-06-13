import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =

      2 := by
  have : (80 : ℝ) = 2 ^ 4 * 5 := by norm_cast
  simp_all only
  simp [show (40 : ℝ) = 2 ^ 3 * 5 by norm_cast, show (160 : ℝ) = 2 ^ 5 * 5 by norm_cast,
    show (20 : ℝ) = 2 ^ 2 * 5 by norm_cast]

  field_simp [Real.log_mul, Real.log_pow] <;> norm_num <;> ring_nf