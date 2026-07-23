import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + abs (a - b) ≤ 1 := by
  have h1 : 2 * (1 - a * b - abs (a - b)) = 2 - 2 * a * b - 2 * abs (a - b) := by
    clear * -
    (field_simp [mabs_of_one_lt] at *)

  have h2 : 2 - 2 * a * b - 2 * abs (a - b) = (a ^ 2 + b ^ 2) + 1 - 2 * a * b - 2 * abs (a - b) := by
    clear * - h₀
    simp_all only [sub_left_inj]
    (grind only [sq_abs])

  have h3 : (a ^ 2 + b ^ 2) + 1 - 2 * a * b - 2 * abs (a - b) = (a ^ 2 - 2 * a * b + b ^ 2) + 1 - 2 * abs (a - b) := by
    clear * -
    simp_all only [sub_left_inj]
    (linarith)

  have h4 : (a ^ 2 - 2 * a * b + b ^ 2) + 1 - 2 * abs (a - b) = (a - b) ^ 2 + 1 - 2 * abs (a - b) := by
    clear * -
    simp_all only [sub_left_inj, add_left_inj]
    (nlinarith)

  have h5 : (a - b) ^ 2 + 1 - 2 * abs (a - b) = (abs (a - b)) ^ 2 + 1 - 2 * abs (a - b) := by
    clear * -
    simp only [sq_abs] at *

  have h6 : (abs (a - b)) ^ 2 + 1 - 2 * abs (a - b) = (abs (a - b) - 1) ^ 2 := by
    clear * -
    simp_all only [sq_abs]
    (grind only [sq_abs])

  have h7 : (abs (a - b) - 1) ^ 2 ≥ 0 := by
    clear * -
    apply pow_two_nonneg

  have h8 : 2 * (1 - a * b - abs (a - b)) ≥ 0 := by
    clear * - h1 h2 h3 h4 h5 h6 h7
    simp_all only [sq_abs, sub_left_inj, add_left_inj, ge_iff_le]

  have h9 : 1 - a * b - abs (a - b) ≥ 0 := by
    clear * - h8
    simp_all only [ge_iff_le, ofNat_pos, mul_nonneg_iff_of_pos_left, sub_nonneg]

  have h10 : a * b + abs (a - b) ≤ 1 := by
    clear * - h9
    simp_all only [ge_iff_le, sub_nonneg]
    (grind only [max_sub_max_le_max])

  exact h10
