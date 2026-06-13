import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

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
    norm_num

  have h₇ : 17 ∣ n ! := by
    clear * - h₁ h₅ h₆
    simp_all only [reducePow, reduceMul]
    (omega)

  have h₈ : Nat.Prime 17 → 17 ∣ n ! → 17 ≤ n := by
    clear * - h₆
    simp_all only [forall_const]
    contrapose! h₆
    norm_num
    rcases h₆ with ⟨h₁, h₂⟩
    interval_cases n <;> norm_cast <;> decide

  have h₉ : 17 ≤ n := by
    clear * - h₇ h₈
    simp_all only [forall_const]
    (norm_num [*] at *)

  exact h₉