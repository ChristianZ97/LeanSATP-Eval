
import Mathlib

set_option maxHeartbeats 0

abbrev putnam_1999_a1_solution : Prop := True
theorem putnam_1999_a1
: putnam_1999_a1_solution ↔ ∃ f g h : Polynomial ℝ, ∀ x : ℝ, |f.eval x| - |g.eval x| + h.eval x = if x < -1 then -1 else (if (x ≤ 0) then 3 * x + 2 else -2 * x + 2) := by
  constructor
  · -- Direction 1: True -> Existence
    intro h_trivial
    let A : ℝ := (3 : ℝ) / 2
    let B : ℝ := (-5 : ℝ) / 2
    let C : ℝ := (-1 : ℝ)
    let D : ℝ := (1 : ℝ) / 2
    let f : Polynomial ℝ := Polynomial.C A * Polynomial.X + Polynomial.C A
    let g : Polynomial ℝ := Polynomial.C (-B) * Polynomial.X -- -B = 5/2
    let h_poly : Polynomial ℝ := -Polynomial.X + Polynomial.C D
    use f, g, h_poly
    intro x
    simp_all only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, map_neg, neg_mul,
      Polynomial.eval_neg, abs_neg, one_div, f, A, g, B, h_poly, D]

    split_ifs <;> ring_nf <;> ring
    · simp_all only [one_div]
      cases' abs_cases (3 / 2 + x * (3 / 2)) with h h <;> cases' abs_cases (x * (-5 / 2)) with h' h' <;> linarith

    · simp_all only [not_lt, one_div]
      cases abs_cases (3 / 2 + x * (3 / 2)) <;> cases abs_cases (x * (-5 / 2)) <;> nlinarith

    · simp_all only [not_lt, not_le, one_div]
      cases' abs_cases (3 / 2 + x * (3 / 2)) with h h <;> cases' abs_cases (x * (-5 / 2)) with h' h' <;> nlinarith

  · -- Direction 2: Existence -> True
    intro h
    trivial