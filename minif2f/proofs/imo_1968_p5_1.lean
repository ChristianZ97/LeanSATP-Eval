import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a) (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) (h₂ : ∀ x, f x - f x ^ 2 ≥ 0) : ∃ b > 0, ∀ x, f (x + b) = f x := by
  have h_sqrt_nonneg : ∀ x, Real.sqrt (f x - f x ^ 2) ≥ 0 := by
    clear * -
    intro x
    (ring)
    (bound )

  have h_fa_ge_half : ∀ x, f (x + a) ≥ (1:ℝ) / 2 := by
    clear * - h₁ h_sqrt_nonneg
    intro x
    simp_all only [one_div, ge_iff_le, Real.sqrt_nonneg, implies_true, le_add_iff_nonneg_right]

  have h_f_ge_half : ∀ x, f x ≥ (1:ℝ) / 2 := by
    clear * - h_fa_ge_half
    intro c
    have := h_fa_ge_half (c - a) <;> aesop

  let g := fun x => 2 * f x - (1:ℝ)

  have h_g_nonneg : ∀ x, g x ≥ 0 := by
    clear * - h_f_ge_half
    exact fun i => by linarith [h_f_ge_half i]

  have h_one_minus_g_sq_nonneg : ∀ x, (1:ℝ) - g x ^ 2 ≥ 0 := by
    clear * - h₂
    intro x₁
    nlinarith [h₂ (x₁), h₂ (-x₁ + 1)]

  have h_f_inverse : ∀ x, f x = (g x + (1:ℝ)) / (2:ℝ) := by
    clear * -
    simp_all only [sub_add_cancel, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, implies_true, g]

  have h_term_identity : ∀ x, f x - f x ^ 2 = ((1:ℝ) - g x ^ 2) / (4:ℝ) := by
    clear * - h_f_inverse h_one_minus_g_sq_nonneg
    intro c
    nlinarith [h_one_minus_g_sq_nonneg c]

  have h_g_recurrence : ∀ x, g (x + a) = Real.sqrt ((1:ℝ) - g x ^ 2) := by
    clear * - h₁ h_term_identity h_one_minus_g_sq_nonneg
    intro x
    simp_all only [g]
    (simp_all)
    (nlinarith)

  have h_g_sq_relation : ∀ x, g (x + a) ^ 2 = (1:ℝ) - g x ^ 2 := by
    clear * - h_g_recurrence h_one_minus_g_sq_nonneg
    simp_all only [g]
    (bound )
    (simp_all)

  have h_g_2a_intermediate : ∀ x, g (x + 2 * a) = Real.sqrt (g x ^ 2) := by
    clear * - h_g_recurrence h_g_sq_relation
    simp_all only [g]
    (grind only [Real.sqrt_mul])

  have h_sqrt_sq_simp : ∀ x, Real.sqrt (g x ^ 2) = g x := by
    clear * - h_g_nonneg
    intro x
    simp_all only [g]
    (simp_all)

  have h_g_periodic : ∀ x, g (x + 2 * a) = g x := by
    clear * - h_g_2a_intermediate h_sqrt_sq_simp
    intro x
    simp_all only [g]

  have h_f_periodic : ∀ x, f (x + 2 * a) = f x := by
    clear * - h_g_periodic
    (grind only [two_mul])

  have h_b_pos : 0 < (2:ℝ) * a := by
    clear * - h₀
    (linarith)

  refine' ⟨(2:ℝ) * a, h_b_pos, _⟩
  exact h_f_periodic
