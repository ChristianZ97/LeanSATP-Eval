import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem aime_1988_p8 (f : ℕ → ℕ → ℝ) (h₀ : ∀ x, 0 < x → f x x = x)
    (h₁ : ∀ x y, 0 < x ∧ 0 < y → f x y = f y x)
    (h₂ : ∀ x y, 0 < x ∧ 0 < y → (↑x + ↑y) * f x y = y * f x (x + y)) : f 14 52 = 364 := by
  have h_step1 : f 14 52 = (↑52 / ↑38 : ℝ) * f 14 38 := by
    clear * - h₂
    simp_all only [and_imp]
    have eq₁ := h₂ 14 38 (by norm_num) (by norm_num)
    simp_all only [Nat.cast_ofNat, reduceAdd]
    linarith <;> norm_num1

  have h_step2 : f 14 38 = (↑38 / ↑24 : ℝ) * f 14 24 := by
    clear * - h₂
    simp_all only [and_imp]
    have aux := h₂ 14 24
    simp_all only [ofNat_pos, Nat.cast_ofNat, reduceAdd, forall_const]
    linarith [-38, -24, -14]

  have h_step3 : f 14 24 = (↑24 / ↑10 : ℝ) * f 14 10 := by
    clear * - h₂
    simp_all only [and_imp]
    have := h₂ 14 10 (by norm_cast) (by norm_cast)
    simp_all only [Nat.cast_ofNat, reduceAdd]
    linarith [this, h₂ 10 14 (by positivity) (by positivity)]

  have h_step4 : f 14 10 = f 10 14 := by
    clear * - h₁
    simp_all only [and_imp, ofNat_pos]

  have h_step5 : f 10 14 = (↑14 / ↑4 : ℝ) * f 10 4 := by
    clear * - h₂
    simp_all only [and_imp]
    have aux := h₂ 10 4
    simp_all only [ofNat_pos, Nat.cast_ofNat, reduceAdd, forall_const]
    linarith [h₂ 10 4 (by decide) (by decide)]

  have h_step6 : f 10 4 = f 4 10 := by
    clear * - h₁
    simp_all only [and_imp, ofNat_pos]

  have h_step7 : f 4 10 = (↑10 / ↑6 : ℝ) * f 4 6 := by
    clear * - h₂
    simp_all only [and_imp]
    have aux := h₂ 4 6 (by decide) (by decide)
    simp_all only [Nat.cast_ofNat, reduceAdd]
    linarith <;> norm_num at *

  have h_step8 : f 4 6 = (↑6 / ↑2 : ℝ) * f 4 2 := by
    clear * - h₂
    simp_all only [and_imp]
    have a := h₂ 4 2 (by norm_num) (by norm_num)
    simp_all only [Nat.cast_ofNat, reduceAdd]
    linarith [(by norm_num : (4 : ℝ) + 2 = 6)]

  have h_step9 : f 4 2 = f 2 4 := by
    clear * - h₁
    simp_all only [and_imp, ofNat_pos]

  have h_step10 : f 2 4 = (↑4 / ↑2 : ℝ) * f 2 2 := by
    clear * - h₂
    simp_all only [and_imp]
    have hh₂ := h₂ 2 2
    simp_all only [ofNat_pos, Nat.cast_ofNat, reduceAdd, forall_const]
    linarith [h₂ 2 4 (by positivity) (by positivity)]

  have h_step11 : f 2 2 = (2 : ℝ) := by
    clear * - h₀
    simp_all only [ofNat_pos, Nat.cast_ofNat]

  have h_step12 : f 14 52 = (↑52 / ↑38 : ℝ) * (↑38 / ↑24 : ℝ) * (↑24 / ↑10 : ℝ) *
                      (↑14 / ↑4 : ℝ) * (↑10 / ↑6 : ℝ) * (↑6 / ↑2 : ℝ) *
                      (↑4 / ↑2 : ℝ) * (2 : ℝ) := by
    clear * - h_step1 h_step2 h_step3 h_step4 h_step5 h_step6 h_step7 h_step8 h_step9 h_step10 h_step11
    simp_all only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.div_mul_cancel]
    (field_simp)
    (nlinarith)

  have h_step13 : (↑52 / ↑38 : ℝ) * (↑38 / ↑24 : ℝ) * (↑24 / ↑10 : ℝ) *
                  (↑14 / ↑4 : ℝ) * (↑10 / ↑6 : ℝ) * (↑6 / ↑2 : ℝ) *
                  (↑4 / ↑2 : ℝ) * (2 : ℝ) = (364 : ℝ) := by
    clear * -
    (ring)

  have h_final : f 14 52 = 364 := by
    calc
    f 14 52 = (↑52 / ↑38 : ℝ) * (↑38 / ↑24 : ℝ) * (↑24 / ↑10 : ℝ) *
    (↑14 / ↑4 : ℝ) * (↑10 / ↑6 : ℝ) * (↑6 / ↑2 : ℝ) *
    (↑4 / ↑2 : ℝ) * (2 : ℝ) := h_step12

    _ = (364 : ℝ) := h_step13

  exact h_final