import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12_2000_p1 (i m o : ℕ) (h₀ : i ≠ m ∧ m ≠ o ∧ o ≠ i) (h₁ : i * m * o = 2001) :
    i + m + o ≤ 671 := by
  have h1 : (3 : ℕ) * 23 * 29 = 2001 := by
    clear * -
    simp_all only [reduceMul]

  have h2 : 1 * 3 * 667 = 2001 := by
    clear * -
    simp_all only [one_mul, reduceMul]

  have h3 : 1 + 3 + 667 = 671 := by
    clear * -
    simp only [reduceAdd] at *

  have h4 : 1 * 23 * 87 = 2001 := by
    clear * -
    simp_all only [one_mul, reduceMul]

  have h5 : 1 + 23 + 87 = 111 := by
    clear * -
    simp_all only [reduceAdd]

  have h6 : 1 * 29 * 69 = 2001 := by
    clear * -
    simp_all only [one_mul, reduceMul]

  have h7 : 1 + 29 + 69 = 99 := by
    clear * -
    simp_all only [reduceAdd]

  have h8 : 3 * 23 * 29 = 2001 := by
    clear * -
    simp_all only [reduceMul]

  have h9 : 3 + 23 + 29 = 55 := by
    clear * -
    simp only [reduceAdd] at *

  have h10 : 671 ≥ 111 := by
    clear * -
    simp only [ge_iff_le, reduceLeDiff] at *

  have h11 : 111 ≥ 99 := by
    clear * -
    simp only [ge_iff_le, reduceLeDiff] at *

  have h12 : 99 ≥ 55 := by
    clear * -
    simp only [ge_iff_le, reduceLeDiff] at *

  have h_result : i + m + o ≤ 671 := by
    clear * - h₀ h₁ h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp_all only [ne_eq, one_mul, reduceAdd, reduceMul, ge_iff_le, reduceLeDiff]
    cases i <;> cases m <;> cases o <;> aesop
    by_contra h₂
    simp_all only [not_le]
    obtain (_ | _ | n) := n <;> obtain (_ | _ | n₁) := n_1 <;> obtain (_ | _ | n₂) := n_2 <;> ring_nf at h₁ h₂ ⊢ <;> omega

  exact h_result