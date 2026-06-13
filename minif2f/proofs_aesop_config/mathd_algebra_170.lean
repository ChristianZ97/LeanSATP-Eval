import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
    S.card = 11 := by
  simp_all only [Int.reduceDiv, add_zero]
  have hex : S = Finset.Icc (-3) 7
  · ext m <;> aesop
    · cases' abs_cases (m - 2) with k k <;> cases k <;> omega
    · cases' abs_cases (m - 2) with k k <;> linarith
    · cases abs_cases (m - 2) <;> all_goals omega

  · simp_all only [Int.reduceNeg, Finset.mem_Icc, Int.card_Icc, Int.reduceAdd, sub_neg_eq_add, Int.reduceToNat]