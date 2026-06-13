import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by
  have h_sub_v : i * z = 1 + Complex.I := by
    clear * - h₀ h₁
    subst h₁
    simp_all only

  have h_sub_z : i * (2 - Complex.I) = 1 + Complex.I := by
    clear * - h₂ h_sub_v
    subst h₂
    simp_all only

  have h_nonzero : 2 - Complex.I ≠ 0 := by
    clear * -
    simp_all only [ne_eq]
    norm_num [Complex.ext_iff]

  have h_isolated : i = (1 + Complex.I) / (2 - Complex.I) := by
    clear * - h_sub_z h_nonzero
    simp_all only [ne_eq]
    (field_simp)
    simp_all only

  have h_denom_calc : (2 - Complex.I) * (2 + Complex.I) = (5 : ℂ) := by
    clear * -
    (ring_nf at *)
    simp_all only [Complex.I_sq, sub_neg_eq_add]
    (ring_nf at *)

  have h_num_calc : (1 + Complex.I) * (2 + Complex.I) = 1 + 3 * Complex.I := by
    clear * -
    (ring_nf at *)
    simp_all only [Complex.I_sq]
    (ring_nf at *)

  have h_rationalized : (1 + Complex.I) / (2 - Complex.I) = (1 + 3 * Complex.I) / (5 : ℂ) := by
    clear * - h_denom_calc h_num_calc
    field_simp [h_denom_calc, h_num_calc]
    rw [← h_num_calc, div_eq_iff] <;> ring
    · simp_all only [Complex.I_sq, neg_neg]
      simp [_root_.pow_three] <;> ring
    · simp_all only [ne_eq]
      rw [Complex.ext_iff]
      simp_all

  have h_distributed : (1 + 3 * Complex.I) / (5 : ℂ) = (1 : ℂ) / (5 : ℂ) + (3 : ℂ) / (5 : ℂ) * Complex.I := by
    clear * -
    simp_all only [one_div]
    (field_simp)

  have h_final : i = 1 / 5 + 3 / 5 * Complex.I := by
    clear * - h_isolated h_rationalized h_distributed
    subst h_isolated
    simp_all only [one_div]

  exact h_final
