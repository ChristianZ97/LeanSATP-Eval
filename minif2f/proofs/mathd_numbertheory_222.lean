import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_222 (b : ℕ) (h₀ : Nat.lcm 120 b = 3720) (h₁ : Nat.gcd 120 b = 8) :
    b = 248 := by
  have h_step1 : (120 : ℕ) * b = Nat.gcd 120 b * Nat.lcm 120 b := by
    clear * -
    apply Eq.symm
    apply Nat.gcd_mul_lcm

  have h_step2 : (120 : ℕ) * b = 8 * 3720 := by
    clear * - h_step1 h₀ h₁
    simp_all only [reduceMul]

  have h_step3 : 8 * 3720 = 29760 := by
    clear * -
    simp_all only [reduceMul]

  have h_step4 : (120 : ℕ) * b = 29760 := by
    clear * - h_step2 h_step3
    simp_all only [reduceMul]

  have h_step5 : b = (29760 : ℕ) / (120 : ℕ) := by
    clear * - h_step4
    simp_all only [reduceDiv]
    (nlinarith)

  have h_lemma_simp : (29760 : ℕ) / (120 : ℕ) = (2976 : ℕ) / (12 : ℕ) := by
    clear * -
    simp_all only [reduceDiv]

  have h_step6 : b = (2976 : ℕ) / (12 : ℕ) := by
    clear * - h_step5 h_lemma_simp
    subst h_step5
    simp_all only [reduceDiv]

  have h_lemma_eval : (2976 : ℕ) / (12 : ℕ) = 248 := by
    clear * -
    simp_all only [reduceDiv]

  have h_step7 : b = 248 := by
    clear * - h_step6 h_lemma_eval
    subst h_step6
    simp_all only [reduceDiv]

  exact h_step7