import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  have h₁ : 0 ≤ x := by
    by_contra! h_neg
    by_cases h_case1 : x < (-1:ℝ)
    · -- Case x < -1
      have h₂ : abs (x - 1) = -(x - 1) := by
        apply abs_of_neg
        linarith

      have h₃ : abs x = -x := by
        apply abs_of_neg
        exact h_neg

      have h₄ : abs (x + 1) = -(x + 1) := by
        apply abs_of_neg
        linarith

      have h₅ : -(x - 1) + (-x) + (-(x + 1)) = x + 2 := by
        calc
        -(x - 1) + (-x) + (-(x + 1)) = abs (x - 1) + abs x + abs (x + 1) := by rw [h₂, h₃, h₄]
        _ = x + 2 := by rw [h₀]

      have h₆ : -3 * x = x + 2 := by linarith
      have h₇ : x = (-1/2:ℝ) := by linarith
      linarith

    · -- Case -1 <= x < 0
      have h₂ : abs (x - 1) = -(x - 1) := by
        apply abs_of_neg
        linarith

      have h₃ : abs x = -x := by
        apply abs_of_neg
        exact h_neg

      have h₄ : abs (x + 1) = x + 1 := by
        apply abs_of_nonneg
        linarith

      have h₅ : -(x - 1) + (-x) + (x + 1) = x + 2 := by
        calc
        -(x - 1) + (-x) + (x + 1) = abs (x - 1) + abs x + abs (x + 1) := by rw [h₂, h₃, h₄]
        _ = x + 2 := by rw [h₀]

      have h₆ : 2 - x = x + 2 := by linarith
      have h₇ : x = 0 := by linarith
      linarith

  have h₂ : x ≤ 1 := by
    by_contra! h_gt
    have h₃ : abs (x - 1) = x - 1 := by
      apply abs_of_nonneg
      linarith

    have h₄ : abs x = x := by
      apply abs_of_nonneg
      linarith

    have h₅ : abs (x + 1) = x + 1 := by
      apply abs_of_nonneg
      linarith

    have h₆ : (x - 1) + x + (x + 1) = x + 2 := by
      calc
      (x - 1) + x + (x + 1) = abs (x - 1) + abs x + abs (x + 1) := by rw [h₃, h₄, h₅]
      _ = x + 2 := by rw [h₀]

    have h₇ : 3 * x = x + 2 := by linarith
    have h₈ : x = (1:ℝ) := by linarith
    linarith

  constructor <;> assumption