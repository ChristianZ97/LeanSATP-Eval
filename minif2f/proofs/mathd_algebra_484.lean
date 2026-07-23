import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have h1 : (27 : ℝ) = (3 : ℝ) ^ 3 := by
    clear * -
    (linarith)

  have h2 : Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ 3) := by
    clear * - h1
    simp_all only [Real.log_pow, Nat.cast_ofNat]

  have h3 : Real.log ((3 : ℝ) ^ 3) = (3 : ℝ) * Real.log (3 : ℝ) := by
    clear * -
    (simp_all [Real.log_rpow])

  have h4 : Real.log (27 : ℝ) / Real.log (3 : ℝ) = ((3 : ℝ) * Real.log (3 : ℝ)) / Real.log (3 : ℝ) := by
    clear * - h2 h3
    simp_all only [Real.log_pow, Nat.cast_ofNat]

  have h5 : ((3 : ℝ) * Real.log (3 : ℝ)) / Real.log (3 : ℝ) = (3 : ℝ) := by
    clear * -
    (field_simp [*] at *)

  have h_final : Real.log 27 / Real.log 3 = 3 := by
    clear * - h4 h5
    simp_all only

  exact h_final
