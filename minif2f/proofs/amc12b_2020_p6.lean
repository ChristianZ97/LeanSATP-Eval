import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12b_2020_p6 (n : ℕ) (h₀ : 9 ≤ n) : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! := by
  let x : ℕ := n + 1

  have h2 : (n + 2)! = (n + 2) * (n + 1) * (n)! := by
    clear * -
    (simp [Nat.mul_succ] at *)
    (grind only [Nat.factorial_succ])

  have h3 : (n + 1)! = (n + 1) * (n)! := by
    clear * -
    (simp [Nat.succ_mul] at *)
    (grind only [Nat.factorial_succ])

  have h4 : ((n + 2)! - (n + 1)! : ℝ) = ((n + 2) * (n + 1) * (n)! - (n + 1) * (n)! : ℝ) := by
    clear * - h2 h3
    simp_all only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]

  have h5 : ((n + 2) * (n + 1) * (n)! - (n + 1) * (n)! : ℝ) = ((n)! : ℝ) * (((n + 2) * (n + 1) - (n + 1)) : ℝ) := by
    clear * -
    (linarith)

  have h6 : (((n + 2)! - (n + 1)! : ℝ) / ((n)! : ℝ)) = (((n + 2) * (n + 1) - (n + 1)) : ℝ) := by
    clear * - h4 h5
    simp_all only
    (field_simp [*] at *)

  have h7 : (((n + 2) * (n + 1) - (n + 1)) : ℝ) = ((n + 1) : ℝ) * (((n + 2) - 1) : ℝ) := by
    clear * -
    (linarith)

  have h8 : (((n + 2) - 1) : ℝ) = ((n + 1) : ℝ) := by
    clear * -
    (linarith)

  have h9 : (((n + 2)! - (n + 1)! : ℝ) / ((n)! : ℝ)) = ((n + 1) : ℝ) ^ 2 := by
    clear * - h6 h7 h8
    simp_all only
    (linarith)

  have h10 : ((x : ℝ) ^ 2) = (((n + 2)! - (n + 1)! : ℝ) / ((n)! : ℝ)) := by
    clear * - h9
    simp_all only [Nat.cast_add, Nat.cast_one, x]

  exact ⟨x, h10⟩
