import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_435 (k : ℕ) (h₀ : 0 < k) (h₁ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 3) = 1)
  (h₂ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 2) = 1) (h₃ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 1) = 1) :
  5 ≤ k := by
  by_contra h_neg
  have h_le_4 : k ≤ 4 := by
    clear * - h_neg h₀
    simp_all only [not_le]
    (nlinarith)

  have eval_gcd_4_2 : Nat.gcd 4 2 = 2 := by
    clear * -
    simp_all only [reduceGcd]

  have eval_gcd_3_3 : Nat.gcd 3 3 = 3 := by
    clear * -
    simp only [gcd_self] at *

  have eval_gcd_2_2 : Nat.gcd 2 2 = 2 := by
    clear * -
    simp_all only [gcd_self]

  have eval_gcd_7_7 : Nat.gcd 7 7 = 7 := by
    clear * -
    simp_all only [gcd_self]

  simp_all only [not_le, reduceGcd, gcd_self]
  interval_cases k <;> simp_all [Nat.gcd_comm]
  have h₄ := h₂ 6
  simp_all only [reduceMul, reduceAdd, reduceGcd, OfNat.ofNat_ne_one]