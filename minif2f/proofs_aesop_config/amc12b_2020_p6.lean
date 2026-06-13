import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12b_2020_p6 (n : ℕ) (h₀ : 9 ≤ n) : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! := by
  let x : ℕ := n + 1

  have h2 : (n + 2)! = (n + 2) * (n + 1) * (n)! := by
    clear * -
    simp [factorial, mul_assoc]

  have h3 : (n + 1)! = (n + 1) * (n)! := by
    clear * -
    rfl

  have h4 : ((n + 2)! - (n + 1)! : ℝ) = ((n + 2) * (n + 1) * (n)! - (n + 1) * (n)! : ℝ) := by
    clear * - h2 h3
    simp_all only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]

  have h5 : ((n + 2) * (n + 1) * (n)! - (n + 1) * (n)! : ℝ) = ((n)! : ℝ) * (((n + 2) * (n + 1) - (n + 1)) : ℝ) := by
    clear * -
    (nlinarith)

  have h6 : (((n + 2)! - (n + 1)! : ℝ) / ((n)! : ℝ)) = (((n + 2) * (n + 1) - (n + 1)) : ℝ) := by
    clear * - h4 h5
    simp_all only
    (field_simp)

  have h7 : (((n + 2) * (n + 1) - (n + 1)) : ℝ) = ((n + 1) : ℝ) * (((n + 2) - 1) : ℝ) := by
    clear * -
    (nlinarith)

  have h8 : (((n + 2) - 1) : ℝ) = ((n + 1) : ℝ) := by
    clear * -
    (nlinarith)

  have h9 : (((n + 2)! - (n + 1)! : ℝ) / ((n)! : ℝ)) = ((n + 1) : ℝ) ^ 2 := by
    clear * - h6 h7 h8
    simp_all only
    (nlinarith)

  have h10 : ((x : ℝ) ^ 2) = (((n + 2)! - (n + 1)! : ℝ) / ((n)! : ℝ)) := by
    clear * - h9
    simp_all only [Nat.cast_add, Nat.cast_one, x]

  exact ⟨x, h10⟩