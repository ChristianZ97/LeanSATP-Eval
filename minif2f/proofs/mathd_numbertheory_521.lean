import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  have h_step1 : n = (m : ℕ) - 2 := by
    clear * - h₂
    (omega)

  have h_step2 : m * ((m : ℕ) - 2) = 288 := by
    clear * - h_step1 h₃
    subst h_step1
    simp_all only

  have h_step3 : m ^ 2 - 2 * m = 288 := by
    clear * - h_step2
    rcases m with (_ | _ | m) <;> aesop
    any_goals
    have : m ≤ 288 := by nlinarith
    interval_cases m <;> omega

  have h_step4 : m ^ 2 - 2 * m + 1 = 288 + 1 := by
    clear * - h_step3
    simp_all only [reduceAdd]

  have h_step5 : m ^ 2 - 2 * m + 1 = 289 := by
    clear * - h_step4
    simp_all only [reduceAdd, reduceEqDiff]

  have h_step6 : ((m : ℕ) - 1) ^ 2 = 289 := by
    clear * - h_step5
    simp_all only [reduceEqDiff]
    cases m <;> aesop
    obtain _ | n := n <;> ring_nf at h_step5 ⊢ <;> omega

  have h_step7 : ((m : ℕ) - 1) ^ 2 = 17 ^ 2 := by
    clear * - h_step6
    simp_all only [reducePow]

  have h_step8 : (m : ℕ) - 1 = 17 := by
    clear * - h_step7
    simp_all only [reducePow, pred_eq_succ_iff, reduceAdd]
    have h_sq : (m - 1) ^ 2 = 289 := h_step7
    simp_all only
    cases m <;> simp_all <;> nlinarith

  have h_step9 : m = 18 := by
    clear * - h_step8
    simp_all only [pred_eq_succ_iff, reduceAdd]

  exact h_step9