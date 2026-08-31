import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 := by
  have h1 : ((1 : ℝ) + (4 : ℝ) / (100 : ℝ)) * ↑x = 598 := by
    clear * - h₀
    (linarith)

  have h2 : (((100 : ℝ) / (100 : ℝ)) + (4 : ℝ) / (100 : ℝ)) * ↑x = 598 := by
    clear * - h1
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

  have h3 : (((100 : ℝ) + (4 : ℝ)) / (100 : ℝ)) * ↑x = 598 := by
    clear * - h2
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
    (linarith)

  have h4 : ((104 : ℝ) / (100 : ℝ)) * ↑x = 598 := by
    clear * - h3
    (linarith)

  have h5 : (104 : ℝ) * ↑x = 598 * (100 : ℝ) := by
    clear * - h4
    (linarith)

  have h6 : (104 : ℝ) * ↑x = (59800 : ℝ) := by
    clear * - h5
    simp_all only
    (linarith)

  have h7 : ↑x = (59800 : ℝ) / (104 : ℝ) := by
    clear * - h6
    (linarith)

  have h8 : ↑x = (29900 : ℝ) / (52 : ℝ) := by
    clear * - h7
    simp_all only
    (linarith)

  have h9 : ↑x = (14950 : ℝ) / (26 : ℝ) := by
    clear * - h8
    simp_all only
    (linarith)

  have h10 : ↑x = (7475 : ℝ) / (13 : ℝ) := by
    clear * - h9
    simp_all only
    (linarith)

  have h11 : ↑x = (575 : ℝ) := by
    clear * - h10
    simp_all only
    (linarith)

  have h12 : x = 575 := by
    clear * - h11
    norm_cast at h11 <;> linarith

  exact h12
