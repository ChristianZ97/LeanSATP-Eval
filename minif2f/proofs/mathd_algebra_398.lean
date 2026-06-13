import Mathlib
open BigOperators Real Nat Topology Rat
/-- On planet Larky, 7 ligs = 4 lags, and 9 lags = 20 lugs. How many ligs are equivalent to 80 lugs? Show that it is 63.-/

theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by

    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    (nlinarith)