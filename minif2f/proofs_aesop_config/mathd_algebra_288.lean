import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  have h_step1 : y = (-6 : ℝ) := by
    clear * - h₀ h₁
    classical
    rw [abs_of_neg h₀.2] at h₁
    linarith

  have h_step2 : y - (3 : ℝ) = (-9 : ℝ) := by
    clear * - h_step1
    subst h_step1
    (nlinarith)

  have h_step3 : (y - (3 : ℝ)) ^ 2 = 81 := by
    clear * - h_step2
    simp_all only [even_two, Even.neg_pow]
    (nlinarith)

  have h_step4 : Real.sqrt ((x - (8 : ℝ)) ^ 2 + 81) = 15 := by
    clear * - h₂ h_step3
    simp_all only

  have h_step5 : (x - (8 : ℝ)) ^ 2 + 81 = 225 := by
    clear * - h_step4
    nlinarith [Real.sq_sqrt (by nlinarith : 0 ≤ (x - 8) ^ 2 + 81)]

  have h_step6 : (x - (8 : ℝ)) ^ 2 = 144 := by
    clear * - h_step5
    (nlinarith)

  have h_step7 : x - (8 : ℝ) = (-12 : ℝ) := by
    clear * - h₀ h_step6
    obtain ⟨left, right⟩ := h₀
    (nlinarith)

  have h_step8 : x = (-4 : ℝ) := by
    clear * - h_step7
    (nlinarith)

  have h_step9 : x ^ 2 = 16 := by
    clear * - h_step8
    subst h_step8
    simp_all only [even_two, Even.neg_pow]
    (nlinarith)

  have h_step10 : y ^ 2 = 36 := by
    clear * - h_step1
    subst h_step1
    simp_all only [even_two, Even.neg_pow]
    (nlinarith)

  have h_step11 : x ^ 2 + y ^ 2 = 52 := by
    clear * - h_step9 h_step10
    simp_all only
    (nlinarith)

  have h_step12 : n = 52 := by
    clear * - h₃ h_step11
    simp_all only [ofNat_nonneg, NNReal.zero_le_coe, sqrt_inj]
    ext : 1
    simp_all only [NNReal.coe_ofNat]

  exact h_step12