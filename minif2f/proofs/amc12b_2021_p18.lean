import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12b_2021_p18 (z : ℂ)
    (h₀ : 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z ^ 2 + 1) + 31) :
    z + 6 / z = -2 := by
  have h_expand_1 : Complex.normSq (z + 2) = Complex.normSq z + 4 * Complex.re z + 4 := by
    clear * - h₀
    simp [Complex.normSq, sq, add_mul] at h₀
    simp [Complex.normSq, Complex.add_re, Complex.add_im, h₀] <;> nlinarith

  have h_expand_2 : Complex.normSq (z ^ 2 + 1) = Complex.normSq z ^ 2 + 2 * Complex.re (z ^ 2) + 1 := by
    clear * - h₀
    simp [sq, Complex.normSq]
    symm <;> ring

  have h_poly_eq : (Complex.normSq z) ^ 2 - 10 * Complex.normSq z + 8 * Complex.re z + 2 * Complex.re (z ^ 2) + 40 = 0 := by
    clear * - h₀ h_expand_1 h_expand_2
    simp_all only
    (linarith)

  have h_sum_sq_identity : (Complex.normSq z - 6) ^ 2 + (2 * Complex.re z + 2) ^ 2 = 0 := by
    clear * - h_poly_eq
    simp [Complex.normSq, sq, add_mul, mul_add] at *
    ring_nf at * <;> try linarith

  have h_norm_cond : Complex.normSq z - 6 = 0 := by
    clear * - h_sum_sq_identity
    (nlinarith)

  have h_re_cond : 2 * Complex.re z + 2 = 0 := by
    clear * - h_sum_sq_identity
    (nlinarith)

  have h_norm_val : Complex.normSq z = 6 := by
    clear * - h_norm_cond
    (linarith)

  have h_re_val : Complex.re z = -1 := by
    clear * - h_re_cond
    (linarith)

  have h_conj_sum : z + star z = -(2 : ℂ) := by
    clear * - h_re_val
    simp [Complex.ext_iff, h_re_val] <;> ring

  have h_z_nonzero : z ≠ 0 := by
    clear * - h_norm_val
    simp_all only [ne_eq]
    (bound )
    simp_all only [map_zero, OfNat.zero_ne_ofNat]

  have h_inv_formula : star z = (6 : ℂ) / z := by
    clear * - h_norm_val h_z_nonzero
    have h_conj := h_norm_val
    field_simp [Complex.ext_iff, h_z_nonzero, h_conj]
    aesop  (add norm simp [Complex.normSq])
    simp_all [Complex.ext_iff, mul_comm]

  have h_result : z + (6 : ℂ) / z = -(2 : ℂ) := by
    clear * - h_conj_sum h_inv_formula
    (grind only [two_ne_zero'])

  exact h_result
