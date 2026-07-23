import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem aime_1988_p8 (f : ℕ → ℕ → ℝ) (h₀ : ∀ x, 0 < x → f x x = x)
    (h₁ : ∀ x y, 0 < x ∧ 0 < y → f x y = f y x)
    (h₂ : ∀ x y, 0 < x ∧ 0 < y → (↑x + ↑y) * f x y = y * f x (x + y)) : f 14 52 = 364 := by
  have h_step1 : f 14 52 = (↑52 / ↑38 : ℝ) * f 14 38 := by
    clear * - h₂
    have a := h₂ 14 38
    norm_num at a <;> ring_nf <;> linarith

  have h_step2 : f 14 38 = (↑38 / ↑24 : ℝ) * f 14 24 := by
    clear * - h₂
    have helper := h₂ 14 24
    norm_num at helper <;> nlinarith

  have h_step3 : f 14 24 = (↑24 / ↑10 : ℝ) * f 14 10 := by
    clear * - h₂
    have k := h₂ 14 10
    norm_num [eq_div_iff] at * <;> linarith

  have h_step4 : f 14 10 = f 10 14 := by
    clear * - h₁
    simp_all only [and_imp, ofNat_pos]

  have h_step5 : f 10 14 = (↑14 / ↑4 : ℝ) * f 10 4 := by
    clear * - h₂
    simp_all only [and_imp]
    (grind only [div_mul])

  have h_step6 : f 10 4 = f 4 10 := by
    clear * - h₁
    simp_all only [and_imp, ofNat_pos]

  have h_step7 : f 4 10 = (↑10 / ↑6 : ℝ) * f 4 6 := by
    clear * - h₂
    have a := h₂ 4 6
    norm_num at * <;> linarith [h₂ 4 6]

  have h_step8 : f 4 6 = (↑6 / ↑2 : ℝ) * f 4 2 := by
    clear * - h₂
    simp_all only [and_imp]
    (grind only [two_mul])

  have h_step9 : f 4 2 = f 2 4 := by
    clear * - h₁
    simp only [and_imp] at *
    (bound )

  have h_step10 : f 2 4 = (↑4 / ↑2 : ℝ) * f 2 2 := by
    clear * - h₂
    simp_all only [and_imp]
    (grind only [two_mul])

  have h_step11 : f 2 2 = (2 : ℝ) := by
    clear * - h₀
    (bound )

  have h_step12 : f 14 52 = (↑52 / ↑38 : ℝ) * (↑38 / ↑24 : ℝ) * (↑24 / ↑10 : ℝ) *
                      (↑14 / ↑4 : ℝ) * (↑10 / ↑6 : ℝ) * (↑6 / ↑2 : ℝ) *
                      (↑4 / ↑2 : ℝ) * (2 : ℝ) := by
    clear * - h_step1 h_step2 h_step3 h_step4 h_step5 h_step6 h_step7 h_step8 h_step9 h_step10 h_step11
    simp_all only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.div_mul_cancel]
    (linarith)

  have h_step13 : (↑52 / ↑38 : ℝ) * (↑38 / ↑24 : ℝ) * (↑24 / ↑10 : ℝ) *
                  (↑14 / ↑4 : ℝ) * (↑10 / ↑6 : ℝ) * (↑6 / ↑2 : ℝ) *
                  (↑4 / ↑2 : ℝ) * (2 : ℝ) = (364 : ℝ) := by
    clear * -
    (linarith)

  have h_final : f 14 52 = 364 := by
    calc
      f 14 52 = (↑52 / ↑38 : ℝ) * (↑38 / ↑24 : ℝ) * (↑24 / ↑10 : ℝ) *
                (↑14 / ↑4 : ℝ) * (↑10 / ↑6 : ℝ) * (↑6 / ↑2 : ℝ) *
                (↑4 / ↑2 : ℝ) * (2 : ℝ) := h_step12

      _ = (364 : ℝ) := h_step13

  exact h_final
