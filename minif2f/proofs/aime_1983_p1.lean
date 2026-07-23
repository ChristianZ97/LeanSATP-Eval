import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have h_s1 : Real.log w / Real.log x = (24 : ℝ) := by
    clear * - h0
    simp_all only

  have h_s2 : Real.log x = Real.log w / (24 : ℝ) := by
    clear * - h_s1
    (grind only [Real.Gamma_add_one])

  have h_s3 : Real.log w / Real.log y = (40 : ℝ) := by
    clear * - h1
    simp_all only

  have h_s4 : Real.log y = Real.log w / (40 : ℝ) := by
    clear * - h_s3
    (grind only [mul_div_assoc])

  have h_s5 : Real.log w / Real.log (x * y * z) = (12 : ℝ) := by
    clear * - h2
    simp_all only

  have h_s6 : Real.log (x * y * z) = Real.log w / (12 : ℝ) := by
    clear * - h_s5
    (grind only [mul_div_assoc])

  have h_s7 : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
    clear * - ht
    rw [Real.log_mul, Real.log_mul] <;> aesop

  have h_s8 : Real.log w / (24 : ℝ) + Real.log w / (40 : ℝ) + Real.log z = Real.log w / (12 : ℝ) := by
    clear * - h_s2 h_s4 h_s6 h_s7
    (linarith)

  have h_s9 : (1 : ℝ) / 24 + (1 : ℝ) / 40 + Real.log z / Real.log w = (1 : ℝ) / 12 := by
    clear * - h_s8 ht h0
    (grind only [mul_div_assoc])

  have h_s10 : (1 : ℝ) / 24 + (1 : ℝ) / 40 = (1 : ℝ) / 15 := by
    clear * -
    simp_all only [one_div]
    (linarith)

  have h_s11 : (1 : ℝ) / 15 + Real.log z / Real.log w = (1 : ℝ) / 12 := by
    clear * - h_s9 h_s10
    simp_all only [one_div]

  have h_s12 : Real.log z / Real.log w = (1 : ℝ) / 12 - (1 : ℝ) / 15 := by
    clear * - h_s11
    (linarith)

  have h_s13 : (1 : ℝ) / 12 - (1 : ℝ) / 15 = (1 : ℝ) / 60 := by
    clear * -
    simp_all only [one_div]
    (linarith)

  have h_s14 : Real.log z / Real.log w = (1 : ℝ) / 60 := by
    clear * - h_s12 h_s13
    simp_all only [one_div]

  have h_s15 : Real.log w / Real.log z = (60 : ℝ) := by
    clear * - h_s14
    simp_all only [one_div]
    (grind only [mul_div_assoc])

  exact h_s15
