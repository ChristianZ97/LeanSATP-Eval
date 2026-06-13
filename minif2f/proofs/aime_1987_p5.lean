import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem aime_1987_p5 (x y : ℤ) (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    3 * (x ^ 2 * y ^ 2) = 588 := by
  have h₁ : (y : ℤ)^2 * (1 + 3 * x^2) = 30 * x^2 + 517 := by
    clear * - h₀
    (nlinarith)

  have h₂ : 30 * x^2 + 517 = 10 * (3 * x^2 + 1) + 507 := by
    clear * -
    (nlinarith)

  have h₃ : (y : ℤ)^2 * (1 + 3 * x^2) = 10 * (3 * x^2 + 1) + 507 := by
    clear * - h₁ h₂
    simp_all only

  have h₄ : (y : ℤ)^2 * (1 + 3 * x^2) - 10 * (1 + 3 * x^2) = 507 := by
    clear * - h₃
    simp_all only
    (nlinarith)

  have h₅ : ((y : ℤ)^2 - 10) * (1 + 3 * x^2) = 507 := by
    clear * - h₄
    (nlinarith)

  have h₆ : (507 : ℤ) = 3 * 13^2 := by
    clear * -
    simp_all only [Int.reducePow, Int.reduceMul]

  have h₇ : 1 + 3 * x^2 = 13 := by
    clear * - h₅ h₆
    simp_all only [Int.reducePow, Int.reduceMul]
    have key := sq_nonneg (y ^ 2 - 10)
    have : y ^ 2 - 10 ≤ 507 := by nlinarith
    simp_all only [tsub_le_iff_right, Int.reduceAdd]
    have : y < 26 := by nlinarith
    on_goal 1 =>
      have : y > -26 := by nlinarith
      interval_cases y <;> omega

  have h₈ : 3 * x^2 = 12 := by
    clear * - h₇
    (nlinarith)

  have h₉ : x^2 = 4 := by
    clear * - h₈
    (nlinarith)

  have h₁₀ : (y : ℤ)^2 - 10 = 39 := by
    clear * - h₅ h₇
    simp_all only
    (nlinarith)

  have h₁₁ : (y : ℤ)^2 = 49 := by
    clear * - h₁₀
    (nlinarith)

  have h₁₂ : 3 * (x ^ 2 * y ^ 2) = 3 * 4 * 49 := by
    clear * - h₉ h₁₁
    simp_all only [Int.reduceMul]

  have h₁₃ : 3 * 4 * 49 = 12 * 49 := by
    clear * -
    aesop
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Quaternion.self_add_star | rw [Quaternion.self_add_star] | simp only [Quaternion.self_add_star]))
    (add unsafe 40% (by first | apply Quaternion.star_add_self' | rw [Quaternion.star_add_self'] | simp only [Quaternion.star_add_self']))
    (add unsafe 10% (by first | apply Quaternion.coe_commutes | rw [Quaternion.coe_commutes] | simp only [Quaternion.coe_commutes]))

  have h₁₄ : 12 * 49 = 588 := by
    clear * -
    simp_all only [reduceMul]

  have h₁₅ : 3 * (x ^ 2 * y ^ 2) = 588 := by
    clear * - h₁₂ h₁₃ h₁₄
    simp_all only [Int.reduceMul, reduceMul]

  exact h₁₅
