import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem amc12b_2021_p3 (x : ℝ) (h₀ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53) : x = 3 / 4 := by
  have h₁ : 1 / (1 + 1 / (2 + 2 / (3 + x))) = (144:ℝ) / 53 - 2 := by
    clear * - h₀
    simp_all only [one_div]
    rewrite [← sub_eq_zero]
    field_simp [eq_sub_iff_add_eq] at h₀ ⊢
    simp_all only [one_div]
    ring_nf at *
    rcases eq_or_ne (3 + x) 0 with h₃ | h₃ <;> field_simp [h₃] at * <;> try linarith

  have h₂ : 1 / (1 + 1 / (2 + 2 / (3 + x))) = (38:ℝ) / 53 := by
    clear * - h₁
    simp_all only [one_div]
    (field_simp)
    (nlinarith)

  have h₃ : 1 + 1 / (2 + 2 / (3 + x)) = (53:ℝ) / 38 := by
    clear * - h₂
    simp_all only [one_div]
    have : (38 : ℝ) ≠ 0 := by norm_num
    simp_all
    apply inv_injective
    simp_all only [inv_div]

  have h₄ : 1 / (2 + 2 / (3 + x)) = (53:ℝ) / 38 - 1 := by
    clear * - h₃
    simp_all only [one_div]
    (field_simp)
    (field_simp [*] at *)
    simp_all only [one_div]
    (ring_nf at *)
    (field_simp)
    (field_simp [*] at *)
    (nlinarith)

  have h₅ : 1 / (2 + 2 / (3 + x)) = (15:ℝ) / 38 := by
    clear * - h₄
    simp_all only [one_div]
    (field_simp)
    (nlinarith)

  have h₆ : 2 + 2 / (3 + x) = (38:ℝ) / 15 := by
    clear * - h₅
    simp_all only [one_div]
    try apply Eq.symm
    apply inv_injective
    simp_all only [inv_div]

  have h₇ : 2 / (3 + x) = (38:ℝ) / 15 - 2 := by
    clear * - h₆
    (field_simp)
    (field_simp [*] at *)
    (ring_nf at *)
    (field_simp)
    (field_simp [*] at *)
    (nlinarith)

  have h₈ : 2 / (3 + x) = (8:ℝ) / 15 := by
    clear * - h₇
    simp_all only
    (field_simp)
    (nlinarith)

  have h₉ : (2:ℝ) * (15:ℝ) = (8:ℝ) * ((3:ℝ) + x) := by
    clear * - h₈
    by_cases h : (3 + x) = 0 <;> field_simp [h] at h₈ <;> linarith

  have h₁₀ : (30:ℝ) = (24:ℝ) + (8:ℝ) * x := by
    clear * - h₉
    (nlinarith)

  have h₁₁ : (6:ℝ) = (8:ℝ) * x := by
    clear * - h₁₀
    (nlinarith)

  have h₁₂ : x = (6:ℝ) / 8 := by
    clear * - h₁₁
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]

  have h₁₃ : x = (3:ℝ) / 4 := by
    clear * - h₁₂
    subst h₁₂
    (field_simp)
    (nlinarith)

  exact h₁₃