
import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_11_2_13 (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b := by
  intro h_div_gaussian
  -- Step 1: There exists a Gaussian integer z such that ofInt b = ofInt a * z
  have h_exists_z : ∃ (z : GaussianInt), ofInt b = ofInt a * z := by
    clear * - h_div_gaussian
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 0 (by gcongr))
      (add safe 100 (by interval_cases))
      (add safe 100 (by ring_nf))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Int.natCast_dvd_natCast]))
      (add norm 0 (by grind only [Rat.den_dvd]))
      (add norm 0 (by grind only [Int.ofNat_mul]))
      (add norm 0 (by grind only [Rat.divInt_pow]))
      (add norm 0 (by grind only [Int.dvd_natAbs]))
      (add norm 0 (by rw [Int.gcd_natCast_natCast]))
      (add safe 1 (by simp_all only [Int.natCast_nonneg]))
      (add safe 1 (by simp_all only [Int.natCast_pos]))
      (add safe 1 (by simp_all only [Int.ofNat_eq_coe]))
      (add safe 0 (by simp_all [Num.to_nat_to_int]))
      (add safe 1 (by simp_all only [Rat.ofInt_eq_cast]))
      (add safe 0 (by simp_all [Int.ofNat_lt]))
      (add safe 0 (by simp_all [orderOf_dvd_iff_zpow_eq_one]))
      (add safe 1 (by simp_all only [Rat.mk_eq_divInt]))
      (add safe 0 (by simp_all [ZNum.to_of_int]))
      (add unsafe 50% (by rw [← Int.natCast_pow] at *))
      (add unsafe 50% (by rw [← Int.ofNat_inj] at *))
      (add unsafe 50% (by rw [← Int.natAbs_of_nonneg] at *))
      (add unsafe 50% (by rw [← Int.natAbs] at *))
      (add unsafe 50% (by rw [← Int.natAbs_ofNat] at *))
      (add unsafe 10% (by grind only [Int.ofNat_pos]))
      (add unsafe 50% (by rw [← Int.natCast_natAbs] at *))
      (add unsafe 10% (by grind only [Int.le_of_dvd]))
      (add unsafe 50% (by rw [← ZNum.abs_to_nat] at *))
      (add unsafe 10% (by grind only [Rat.divInt_eq_div]))
      (add unsafe 50% (by rw [← jacobiSym.mod_right] at *))
      (add unsafe 50% (by rw [← Int.eq_natAbs_of_zero_le] at *))
      (add unsafe 10% (by grind only [Rat.mk'_eq_divInt]))
      (add unsafe 10% (by grind only [Int.natCast_mul]))
      (add unsafe 50% (by rw [← Nat.cast_natAbs] at *))
      (add unsafe 50% (by rw [← Int.natCast_inj] at *))
      (add unsafe 10% (by grind only [Int.dvd_of_emod_eq_zero]))

  obtain ⟨z, h_z⟩ := h_exists_z
  -- Let z = x + y*i where x, y are integers
  let x : ℤ := z.re
  let y : ℤ := z.im
  -- Step 2-4: Expand the multiplication in GaussianInt
  -- ofInt b = ofInt (a*x) + ofInt (a*y)*I
  -- So we have two equations from real and imaginary parts:
  -- b = a*x  and  0 = a*y
  have h_real_part : (b : ℤ) = a * x := by
    -- The real part of ofInt b is b, and real part of ofInt a * z is a*x
    simp [ofInt] at h_z
    injection h_z with h_re
    simp at h_re
    exact h_re

  have h_imag_part : (0 : ℤ) = a * y := by
    -- The imaginary part of ofInt b is 0, and imaginary part of ofInt a * z is a*y
    have h_im_part := congrArg Zsqrtd.im h_z
    simp at h_im_part
    cases' h_im_part with h_im_part h_im_part
    · simp [h_im_part]
    · simp [h_im_part]
      right
      revert h_im_part
      exact fun a ↦ a

  -- Step 5: a*y = 0 implies a=0 or y=0
  have h_zero_product : a = 0 ∨ y = 0 := by
    clear * - h_imag_part
    simp at h_imag_part
    exact h_imag_part

  cases h_zero_product with
  | inl h_a_zero =>
    -- Case 6-8: If a = 0, then b = 0, and 0 divides 0
    have h_b_zero : b = 0 := by
      clear * - h_a_zero h_real_part
      aesop (config := {
        maxRuleApplications := 40
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by norm_cast at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 90% (by norm_num [*] at *))
        (add norm 0 (by grind only [Zsqrtd.zero_re]))
        (add norm 0 (by grind only [Zsqrtd.zero_im]))
        (add norm 0 (by grind only [Zsqrtd.norm_zero]))
        (add norm 0 (by grind only [Zsqrtd.gcd_eq_zero_iff]))
        (add norm 0 (by grind only [Zsqrtd.norm_eq_zero]))
        (add norm 0 (by grind only [Int.gcd_eq_zero_iff]))
        (add norm 0 (by grind only [mul_eq_zero]))
        (add norm 0 (by grind only [Zsqrtd.norm_eq_zero_iff]))
        (add norm 0 (by grind only [GaussianInt.toComplex_eq_zero]))
        (add norm 0 (by grind only [Int.natAbs_zero]))
        (add norm 0 (by grind only [pow_eq_zero]))
        (add norm 0 (by grind only [pow_eq_zero_iff]))
        (add norm 0 (by grind only [Int.ofNat_eq_zero]))
        (add norm 0 (by grind only [legendreSym.eq_zero_iff]))
        (add norm 0 (by grind only [Int.natCast_eq_zero]))
        (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
        (add norm 0 (by grind only [Quaternion.normSq_eq_zero]))
        (add norm 0 (by grind only [Int.natAbs_eq_zero]))
        (add norm 0 (by grind only [MulZeroClass]))
        (add norm 0 (by grind only [quadratic_eq_zero_iff_of_discrim_eq_zero]))
        (add norm 0 (by grind only [Int.ediv_zero]))
        (add norm 0 (by grind only [GaussianInt.norm_eq_zero]))
        (add norm 0 (by grind only [Zsqrtd.intCast_im]))
        (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
        (add norm 0 (by grind only [or_self_iff]))
        (add norm 0 (by grind only [Int.zero_mul]))
        (add norm 0 (by grind only [zero_pow]))
        (add norm 0 (by grind only [div_eq_zero_iff]))
        (add norm 0 (by grind only [EuclideanDomain.zero_div]))
        (add norm 0 (by grind only [Int.mul_zero]))
        (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero_z]))
        (add norm 0 (by grind only [lcm_eq_zero_iff]))

    have h_result : a ∣ b := by
      clear * - h_a_zero h_b_zero
      aesop (config := {
        maxRuleApplications := 40
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 100 (by exfalso))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by push_neg))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by norm_cast at *))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Int.natAbs_zero]))
        (add norm 0 (by grind only [Int.gcd_zero_left]))
        (add norm 0 (by grind only [Int.natCast_zero]))
        (add norm 0 (by grind only [Int.gcd_zero_right]))
        (add norm 0 (by grind only [Zsqrtd.zero_im]))
        (add norm 0 (by grind only [Int.gcd_eq_zero_iff]))
        (add norm 0 (by grind only [Int.ediv_zero]))
        (add norm 0 (by grind only [Int.zero_dvd]))
        (add norm 0 (by grind only [Nat.eq_zero_of_gcd_eq_zero_right]))
        (add norm 0 (by grind only [zero_dvd_iff]))
        (add norm 0 (by grind only [Zsqrtd.norm_zero]))
        (add norm 0 (by grind only [Nat.eq_zero_of_gcd_eq_zero_left]))
        (add norm 0 (by grind only [eq_zero_of_zero_dvd]))
        (add norm 0 (by grind only [jacobiSym.zero_right]))
        (add norm 0 (by grind only [Nat.coprime_zero_right]))
        (add norm 0 (by grind only [Int.log_zero_right]))
        (add norm 0 (by grind only [Int.ofNat_zero]))
        (add norm 0 (by grind only [Nat.coprime_zero_left]))
        (add norm 0 (by grind only [not_isCoprime_zero_zero]))
        (add norm 0 (by grind only [Nat.zero_dvd]))
        (add norm 0 (by grind only [Zsqrtd.zero_re]))
        (add norm 0 (by grind only [Nat.not_coprime_zero_zero]))
        (add norm 0 (by grind only [Int.zero_ediv]))
        (add norm 0 (by grind only [Int.natAbs_eq_zero]))
        (add norm 0 (by grind only [Zsqrtd.gcd_eq_zero_iff]))
        (add norm 0 (by grind only [Int.zero_mul]))
        (add norm 0 (by grind only [Int.dvd_zero]))
        (add norm 0 (by grind only [Int.natCast_eq_zero]))
        (add norm 0 (by grind only [Nat.dvd_zero]))
        (add norm 0 (by grind only [Int.zero_mod]))
        (add norm 0 (by grind only [Nat.gcd_zero_left]))
        (add norm 0 (by grind only [gcd_zero_left']))

    exact h_result

  | inr h_y_zero =>
    -- Case 9-12: If a ≠ 0, then y = 0, so b = a*x, hence a divides b
    have h_a_nonzero_or_y_zero : a ≠ 0 ∨ y = 0 := by
      clear * - h_y_zero
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by exfalso))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by norm_cast at *))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Zsqrtd.zero_im]))
        (add norm 0 (by grind only [Zsqrtd.zero_re]))
        (add norm 0 (by grind only [GaussianInt.toComplex_eq_zero]))
        (add norm 0 (by grind only [Real.logb_eq_zero]))
        (add norm 0 (by grind only [or_self_iff]))
        (add norm 0 (by grind only [mul_eq_zero]))
        (add norm 0 (by grind only [GaussianInt.toComplex_zero]))
        (add norm 0 (by grind only [Zsqrtd.norm_zero]))
        (add norm 0 (by grind only [Zsqrtd.norm_eq_zero]))
        (add norm 0 (by grind only [false_or_iff]))
        (add norm 0 (by grind only [Complex.ext_iff]))
        (add norm 0 (by grind only [or_self]))
        (add norm 0 (by grind only [div_eq_zero_iff]))
        (add norm 0 (by grind only [Int.natCast_eq_zero]))
        (add norm 0 (by grind only [Int.gcd_eq_zero_iff]))
        (add norm 0 (by grind only [or_iff_left]))
        (add norm 0 (by grind only [or_false_iff]))
        (add norm 0 (by grind only [or_not]))
        (add norm 0 (by grind only [Hyperreal.infinitesimal_real_iff]))
        (add norm 0 (by grind only [ArithmeticFunction.moebius_eq_or]))
        (add norm 0 (by grind only [Real.log_eq_zero]))
        (add norm 0 (by grind only [Zsqrtd.norm_eq_zero_iff]))
        (add norm 0 (by grind only [Matrix.zero_zpow]))
        (add norm 0 (by grind only [Int.ofNat_eq_zero]))
        (add norm 0 (by grind only [GaussianInt.norm_eq_zero]))
        (add norm 0 (by grind only [inv_eq_zero]))
        (add norm 0 (by grind only [Quaternion.normSq_eq_zero]))
        (add norm 0 (by grind only [or_false]))
        (add norm 0 (by grind only [false_or]))
        (add norm 0 (by grind only [GaussianInt.toComplex_inj]))
        (add norm 0 (by grind only [Complex.zero_im]))
        (add norm 0 (by grind only [Real.sin_eq_zero_iff_cos_eq]))

    -- We know y = 0 from h_y_zero
    have h_b_equals_ax : b = a * x := by
      clear * - h_real_part
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        maxGoals := 512
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 0 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero_z]))
        (add norm 0 (by grind only [Zsqrtd]))
        (add norm 0 (by grind only [Int.mul_ediv_cancel_left]))
        (add norm 0 (by grind only [Int.natCast_mul]))
        (add norm 0 (by grind only [Int.mul_assoc]))
        (add norm 0 (by grind only [Int.mul_ediv_cancel]))
        (add norm 0 (by grind only [Int.gcd_eq_gcd_ab]))
        (add norm 0 (by grind only [Int.natAbs_mul_self]))
        (add norm 0 (by grind only [Int.mul_comm]))
        (add norm 0 (by grind only [Int.mul_eq_mul_left_iff]))
        (add norm 0 (by grind only [Int.ediv_self]))
        (add norm 0 (by grind only [Int.mul_eq_zero]))
        (add norm 0 (by grind only [Int.sq_of_gcd_eq_one]))
        (add norm 0 (by grind only [Int.mul_left_comm]))
        (add norm 0 (by grind only [Int.add_mul]))
        (add norm 0 (by grind only [Int.eq_mul_of_ediv_eq_left]))
        (add norm 0 (by grind only [Int.eq_mul_of_ediv_eq_right]))
        (add norm 0 (by grind only [Int.gcd]))
        (add norm 0 (by grind only [Zsqrtd.smul_val]))
        (add norm 0 (by grind only [Zsqrtd.divides_sq_eq_zero]))
        (add norm 0 (by grind only [Zsqrtd.norm]))
        (add norm 0 (by grind only [Int.ediv_eq_iff_eq_mul_left]))
        (add norm 0 (by grind only [Rat.divInt_one]))
        (add norm 0 (by grind only [Int.ofNat_ne_zero]))
        (add norm 0 (by grind only [Rat.divInt_self']))
        (add norm 0 (by grind only [Zsqrtd.norm_def]))
        (add norm 0 (by grind only [Int.ediv_one]))
        (add norm 0 (by grind only [Int.sqrt_eq]))
        (add norm 0 (by grind only [Pell.isPell_norm]))
        (add norm 0 (by grind only [mul_eq_mul_left_iff]))
        (add norm 0 (by grind only [Rat.divInt_eq_iff]))
        (add norm 0 (by grind only [Int.ediv_mul_cancel]))

    -- Since b = a * x and x is an integer, a divides b
    simp only [h_b_equals_ax, dvd_mul_right]
