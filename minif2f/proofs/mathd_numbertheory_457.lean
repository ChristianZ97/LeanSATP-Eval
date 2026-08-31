import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_numbertheory_457 (n : ℕ) (h₀ : 0 < n) (h₁ : 80325 ∣ n !) : 17 ≤ n := by
  have h₂ : 80325 = 25 * 3213 := by
    clear * -
    simp_all only [reduceMul]

  have h₃ : 3213 = 27 * 119 := by
    clear * -
    simp_all only [reduceMul]

  have h₄ : 119 = 7 * 17 := by
    clear * -
    simp_all only [reduceMul]

  have h₅ : 80325 = 5^2 * 3^3 * 7 * 17 := by
    clear * - h₂ h₃ h₄
    simp_all only [reduceMul, reducePow]

  have h₆ : Nat.Prime 17 := by
    clear * -
    (bound )

  have h₇ : 17 ∣ n ! := by
    clear * - h₁ h₅ h₆
    simp only [reducePow, reduceMul] at *
    (omega)

  have h₈ : Nat.Prime 17 → 17 ∣ n ! → 17 ≤ n := by
    clear * - h₆
    intro p hp
    contrapose! hp
    interval_cases n <;> norm_cast <;> native_decide

  have h₉ : 17 ≤ n := by
    clear * - h₇ h₈
    (bound )

  exact h₉
