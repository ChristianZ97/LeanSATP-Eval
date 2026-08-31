import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12a_2021_p3 (x y : ℕ) (h₀ : x + y = 17402) (h₁ : 10 ∣ x) (h₂ : x / 10 = y) :
    ↑x - ↑y = (14238 : ℤ) := by
  have h3 : x = 10 * y := by
    clear * - h₁ h₂
    subst h₂
    (omega)

  have h4 : 10 * y + y = 17402 := by
    clear * - h₀ h3
    subst h3
    simp_all only

  have h5 : 11 * y = 17402 := by
    clear * - h4
    (linarith)

  have h6 : 17402 = 11 * 1582 := by
    clear * -
    simp_all only [reduceMul]

  have h7 : y = 1582 := by
    clear * - h5 h6
    simp_all only [reduceMul]
    (linarith)

  have h8 : x = 10 * 1582 := by
    clear * - h3 h7
    subst h3 h7
    simp_all only [reduceMul]

  have h9 : x = 15820 := by
    clear * - h8
    subst h8
    simp_all only [reduceMul]

  have h10 : ↑x - ↑y = (14238 : ℤ) := by
    clear * - h9 h7
    subst h7 h9
    simp_all only [Nat.cast_ofNat, Int.reduceSub]

  exact h10
