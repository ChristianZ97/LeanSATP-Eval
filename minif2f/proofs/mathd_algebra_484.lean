import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have h1 : (27 : ℝ) = (3 : ℝ) ^ 3 := by
    clear * -
    aesop
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Int.cast_two | rw [Int.cast_two] | simp only [Int.cast_two]))
    (add unsafe 30% (by first | apply Complex.cpow_two | rw [Complex.cpow_two] | simp only [Complex.cpow_two]))
    (add unsafe 30% (by first | apply Nat.factorial_two | rw [Nat.factorial_two] | simp only [Nat.factorial_two]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
    (add unsafe 10% (by first | apply Nat.cast_two | rw [Nat.cast_two] | simp only [Nat.cast_two]))

  have h2 : Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ 3) := by
    clear * - h1
    simp_all only [Real.log_pow, Nat.cast_ofNat]

  have h3 : Real.log ((3 : ℝ) ^ 3) = (3 : ℝ) * Real.log (3 : ℝ) := by
    clear * -
    simp_all only [Real.log_pow, Nat.cast_ofNat]

  have h4 : Real.log (27 : ℝ) / Real.log (3 : ℝ) = ((3 : ℝ) * Real.log (3 : ℝ)) / Real.log (3 : ℝ) := by
    clear * - h2 h3
    simp_all only [Real.log_pow, Nat.cast_ofNat]

  have h5 : ((3 : ℝ) * Real.log (3 : ℝ)) / Real.log (3 : ℝ) = (3 : ℝ) := by
    clear * -
    (field_simp)

  have h_final : Real.log 27 / Real.log 3 = 3 := by
    clear * - h4 h5
    simp_all only

  exact h_final
