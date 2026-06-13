
import Mathlib

set_option maxHeartbeats 0

abbrev putnam_1977_a3_solution : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) :=
  fun f g => fun x => g x + f (x + 1) + f (x - 1) - f (x + 3) - f (x - 3)

theorem putnam_1977_a3
    (f g h : ℝ → ℝ)
    (hf : ∀ x, f x = (h (x + 1) + h (x - 1)) / 2)
    (hg : ∀ x, g x = (h (x + 4) + h (x - 4)) / 2) :
    h = putnam_1977_a3_solution f g := by
  have hf_x_plus_1 : ∀ x, f (x + 1) = (h (x + 2) + h x) / 2 := by
    clear * - hf
    intro x
    simp_all only [add_sub_cancel_right]
    (field_simp)
    (ring_nf at *)

  have hf_x_minus_1 : ∀ x, f (x - 1) = (h x + h (x - 2)) / 2 := by
    clear * - hf
    intro x
    simp_all only [sub_add_cancel]
    (field_simp)
    (ring_nf at *)

  have hf_x_plus_3 : ∀ x, f (x + 3) = (h (x + 4) + h (x + 2)) / 2 := by
    clear * - hf
    intro x
    simp_all only
    (field_simp)
    (ring_nf at *)

  have hf_x_minus_3 : ∀ x, f (x - 3) = (h (x - 2) + h (x - 4)) / 2 := by
    clear * - hf
    intro x
    simp_all only
    (field_simp)
    (ring_nf at *)

  have hg_x : ∀ x, g x = (h (x + 4) + h (x - 4)) / 2 := by
    clear * - hg
    intro x
    simp_all only

  have sum_f_terms : ∀ x, f (x + 1) + f (x - 1) - f (x + 3) - f (x - 3) =
      (h (x + 2) + h x) / 2 + (h x + h (x - 2)) / 2 - (h (x + 4) + h (x + 2)) / 2 - (h (x - 2) + h (x - 4)) / 2 := by
    clear * - hf_x_plus_1 hf_x_minus_1 hf_x_plus_3 hf_x_minus_3
    intro x
    simp_all only

  have simplify_sum : ∀ x, f (x + 1) + f (x - 1) - f (x + 3) - f (x - 3) =
      (2 * h x - h (x + 4) - h (x - 4)) / 2 := by
    clear * - sum_f_terms
    intro x
    simp_all only
    (field_simp)
    (nlinarith)

  have combine_with_g : ∀ x, g x + f (x + 1) + f (x - 1) - f (x + 3) - f (x - 3) = h x := by
    clear * - hg_x simplify_sum
    simp_all only
    exact λ x ↦ by linarith [simplify_sum x]

  have main_eq : ∀ x, h x = putnam_1977_a3_solution f g x := by
    clear * - combine_with_g
    intro x
    simp_all only

  clear * - main_eq
  (bound )