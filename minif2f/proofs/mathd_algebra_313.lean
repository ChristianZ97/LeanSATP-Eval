import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by
  have h_sub_v : i * z = 1 + Complex.I := by
    clear * - h₀ h₁
    subst h₀
    simp_all only

  have h_sub_z : i * (2 - Complex.I) = 1 + Complex.I := by
    clear * - h₂ h_sub_v
    subst h₂
    (omega)

  have h_nonzero : 2 - Complex.I ≠ 0 := by
    clear * -
    simp [Complex.ext_iff]

  have h_isolated : i = (1 + Complex.I) / (2 - Complex.I) := by
    clear * - h_sub_z h_nonzero
    simp_all only [ne_eq]
    (grind only [Complex.ofReal_div])

  have h_denom_calc : (2 - Complex.I) * (2 + Complex.I) = (5 : ℂ) := by
    clear * -
    (ring)
    simp_all only [Complex.I_sq, sub_neg_eq_add]
    (bound )

  have h_num_calc : (1 + Complex.I) * (2 + Complex.I) = 1 + 3 * Complex.I := by
    clear * -
    (ring)
    simp_all only [Complex.I_sq]
    (grind only [Complex.cpow_add])

  have h_rationalized : (1 + Complex.I) / (2 - Complex.I) = (1 + 3 * Complex.I) / (5 : ℂ) := by
    clear * - h_denom_calc h_num_calc
    (grind only [mul_div])

  have h_distributed : (1 + 3 * Complex.I) / (5 : ℂ) = (1 : ℂ) / (5 : ℂ) + (3 : ℂ) / (5 : ℂ) * Complex.I := by
    clear * -
    simp_all only [one_div]
    (grind only [mul_div_cancel_left₀])

  have h_final : i = 1 / 5 + 3 / 5 * Complex.I := by
    clear * - h_isolated h_rationalized h_distributed
    subst h_isolated
    simp_all only [one_div]

  exact h_final
