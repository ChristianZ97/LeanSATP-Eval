import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) (h₁ : 4 ≤ p ∧ p ≤ 18)
    (h₂ : 4 ≤ q ∧ q ≤ 18) : ↑p * ↑q - (↑p + ↑q) ≠ (194 : ℕ) := by
  intro h
  have h1 : ↑p * ↑q - (↑p + ↑q) = (194 : ℤ) := by
    clear * - h
    (omega)

  have h2 : ↑p * ↑q - ↑p - ↑q = (194 : ℤ) := by
    clear * - h1
    (linarith)

  have h3 : ↑p * ↑q - ↑p - ↑q + 1 = (195 : ℤ) := by
    clear * - h2
    simp_all only [Int.reduceAdd]

  have h4 : ((p : ℤ) - 1) * ((q : ℤ) - 1) = (195 : ℤ) := by
    clear * - h3
    (linarith)

  have h5 : (195 : ℤ) % 2 = 1 := by
    clear * -
    simp_all only [Int.reduceMod]

  have h6 : ((p : ℤ) % 2) = 1 := by
    clear * - h₀ h₁
    obtain ⟨hp, hq⟩ := h₀
    rcases h₁ with ⟨h4, h18⟩
    interval_cases p <;> simp_all (config := { decide := true })

  have h7 : ((q : ℤ) % 2) = 1 := by
    clear * - h₀ h₂
    have q_prime := h₀.2
    obtain ⟨h, k⟩ := h₂
    interval_cases q <;> simp_all (config := { decide := true }) [Nat.prime_def_lt]

  have h8 : (((p : ℤ) - 1) % 2) = 0 := by
    clear * - h6
    simp_all only [EuclideanDomain.mod_eq_zero]
    (omega)

  have h9 : (((q : ℤ) - 1) % 2) = 0 := by
    clear * - h7
    simp_all only [EuclideanDomain.mod_eq_zero]
    (omega)

  have h10 : ((((p : ℤ) - 1) * ((q : ℤ) - 1)) % 2) = 0 := by
    clear * - h8 h9
    simp [Int.mul_emod, h8, h9]

  have h11 : False := by
    clear * - h4 h5 h10
    simp_all only [Int.reduceMod, one_ne_zero]

  exfalso
  exact h11
