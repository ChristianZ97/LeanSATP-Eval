
import Mathlib

set_option maxHeartbeats 0

theorem putnam_1968_a1
: 22/7 - Real.pi = ∫ x in (0)..1, x^4 * (1 - x)^4 / (1 + x^2) := by
  have h_expand : ∀ x : ℝ, x^4 * (1 - x)^4 = x^8 - 4*x^7 + 6*x^6 - 4*x^5 + x^4 := by
    intro x
    clear * -
    (nlinarith)

  have h_poly_identity : ∀ x : ℝ, x^8 - 4*x^7 + 6*x^6 - 4*x^5 + x^4 = (x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4) * (1 + x^2) - 4 := by
    intro x
    clear * -
    (nlinarith)

  have h_integrand_decomp : ∀ x : ℝ, x^4 * (1 - x)^4 / (1 + x^2) = x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4 - 4 / (1 + x^2) := by
    intro x
    clear * - h_expand h_poly_identity
    simp_all only
    (field_simp)

  have h_integral_eq : ∫ x in (0)..1, x^4 * (1 - x)^4 / (1 + x^2) = ∫ x in (0)..1, (x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4 - 4 / (1 + x^2)) := by
    clear * - h_integrand_decomp
    simp_all only

  have h_integral_eval : ∫ x in (0)..1, (x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4 - 4 / (1 + x^2)) = (1:ℝ)/7 - (2:ℝ)/3 + 1 - (4:ℝ)/3 + 4 - Real.pi := by
    clear * -
    simp_all only [one_div]
    apply Eq.symm <;> ring
    rw [eq_comm]
    rw [intervalIntegral.integral_add]
    · simp_all only [intervalIntegral.intervalIntegrable_pow, intervalIntegral.intervalIntegrable_inv_one_add_sq,
        IntervalIntegrable.mul_const, intervalIntegral.integral_sub, integral_pow, Nat.reduceAdd, one_pow, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Nat.cast_ofNat, one_div,
        intervalIntegral.integral_mul_const, integral_inv_one_add_sq, Real.arctan_one, Real.arctan_zero,
        isUnit_iff_ne_zero, IsUnit.div_mul_cancel]
      norm_num <;> ring
    · apply Continuous.intervalIntegrable <;> norm_num
      exact (by fun_prop)
    ·
      simp_all only [intervalIntegral.intervalIntegrable_pow, intervalIntegral.intervalIntegrable_inv_one_add_sq,
        IntervalIntegrable.mul_const, IntervalIntegrable.sub]

  have h_arith_group : ((1:ℝ)/7 - (2:ℝ)/3 + 1 - (4:ℝ)/3 + 4 - Real.pi) = ((1:ℝ)/7 + 5 - (6:ℝ)/3 - Real.pi) := by
    clear * -
    simp_all only [one_div, sub_left_inj]
    (field_simp)
    (nlinarith)

  have h_arith_final : ((1:ℝ)/7 + 5 - (6:ℝ)/3 - Real.pi) = ((22:ℝ)/7 - Real.pi) := by
    clear * -
    simp_all only [one_div, sub_left_inj]
    (field_simp)
    (nlinarith)

  have h_main : ∫ x in (0)..1, x^4 * (1 - x)^4 / (1 + x^2) = (22:ℝ)/7 - Real.pi := by
    clear * - h_integral_eq h_integral_eval h_arith_group h_arith_final
    simp_all only [one_div, sub_left_inj]

  exact Eq.symm h_main
