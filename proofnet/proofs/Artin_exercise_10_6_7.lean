
import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_10_6_7 {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := by
  -- Step 1: Since I is non-zero, there exists a non-zero element w in I
  have h_exists_w : ∃ (w : I), w ≠ 0 := by
    clear * - hI
    by_contra! hw
    apply hI
    ext x
    constructor
    · intro hx
      specialize hw ⟨x, hx⟩
      simp at hw
      simp [hw]
    · intro hx
      rw [Ideal.mem_bot] at hx
      rw [hx]
      apply ZeroMemClass.zero_mem

  -- Let's extract such a w and its carrier value
  obtain ⟨w, hw_ne_zero⟩ := h_exists_w
  let w_val : GaussianInt := w.val
  -- Step 2: The conjugate of w_val is in GaussianInt (trivially true by definition)
  -- We don't need to state this explicitly as it's structural
  -- Step 3 & 4 & 5: Compute w * conj(w) which equals norm(w) = a^2 + b^2
  -- Note: In GaussianInt, the norm is defined and we can use it
  -- let norm_w : ℕ := GaussianInt.nrm w_val
  -- The product w * conj(w) as a GaussianInt has real part equal to the norm and imaginary part 0
  -- More precisely, (w_val * star w_val : GaussianInt) has im = 0
  -- But we need to show that this product is in I. Since w ∈ I and I is an ideal,
  -- and star w_val ∈ GaussianInt, we have w_val * star w_val ∈ I if we view w as absorbing multiplication from GaussianInt on the right.
  -- Actually, for ideals in commutative rings (GaussianInt is commutative), if w ∈ I and any g ∈ GaussianInt, then g * w ∈ I.
  -- Here star w_val ∈ GaussianInt, so (star w_val) * w_val ∈ I.
  -- Step: Show that (star w_val) * w_val is in I
  have h_product_in_I : (star w_val * w_val : GaussianInt) ∈ I := by
    clear * - hw_ne_zero
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 520
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Ideal.mul_mem_left]))
      (add norm 0 (by grind only [Ideal.mul_mem_mul]))
      (add norm 0 (by grind only [Ideal.mul_mem_right]))
      (add norm 0 (by grind only [Ideal.pow_mem_pow]))
      (add norm 0 (by grind only [Ideal.mem_colon_singleton]))
      (add norm 0 (by grind only [Ideal.absNorm_mem]))
      (add norm 0 (by grind only [FractionalIdeal.mul_mem_mul]))
      (add norm 0 (by grind only [ClassGroup.mk0_eq_one_iff]))
      (add norm 0 (by grind only [Ideal.span_singleton_mem_isPrincipalSubmonoid]))
      (add norm 0 (by grind only [Ideal.mem_map_of_mem]))
      (add norm 0 (by grind only [FractionalIdeal.coeIdeal_mul]))
      (add norm 0 (by grind only [Ideal.mul_homogeneous_element_mem_of_mem]))
      (add norm 0 (by grind only [ClassGroup.mk0_eq_mk0_iff]))
      (add norm 0 (by grind only [FractionalIdeal.mem_coeIdeal_of_mem]))
      (add norm 0 (by grind only [Submodule.mul_mem_mul]))
      (add norm 0 (by grind only [PadicInt.sub_zmodRepr_mem]))
      (add norm 0 (by grind only [Ideal.mem_span_singleton_self]))
      (add norm 0 (by grind only [AlgebraicClosure.le_maxIdeal]))
      (add norm 0 (by grind only [pow_mem]))
      (add norm 0 (by grind only [Ideal.norm_mem_spanNorm]))
      (add norm 0 (by grind only [Ideal.subset_span]))
      (add norm 0 (by grind only [Ideal.mem_of_one_mem]))
      (add norm 0 (by grind only [prod_mem_ideal_map_of_mem_conductor]))
      (add norm 0 (by grind only [ClassGroup.mk0_eq_mk0_inv_iff]))
      (add norm 0 (by grind only [Ideal.mem_comap]))
      (add norm 0 (by grind only [Ideal.sub_mem]))
      (add norm 0 (by grind only [HomogeneousIdeal.toIdeal_mul]))
      (add norm 0 (by grind only [Ideal.mem_span_singleton']))
      (add norm 0 (by grind only [ValuationSubring.coe_mem_nonunits_iff]))
      (add norm 0 (by grind only [Ideal.zero_mem]))
      (add norm 0 (by grind only [Ideal.add_mem]))
      (add norm 0 (by grind only [AddMemClass]))

  -- Convert this back to an element of type I
  have h_z_in_I : ∃ (z : I), (z : GaussianInt) = star w_val * w_val := by
    clear * - h_product_in_I
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 20
      maxNormIterations := 520
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [ClassGroup.mk0_eq_one_iff]))
      (add norm 0 (by grind only [Ideal.mul_mem_left]))
      (add norm 0 (by grind only [ClassGroup.mk0_eq_mk0_iff]))
      (add norm 0 (by grind only [Ideal.mul_mem_mul]))
      (add norm 0 (by grind only [Ideal.absNorm_mem]))
      (add norm 0 (by grind only [AlgebraicClosure.le_maxIdeal]))
      (add norm 0 (by grind only [Ideal.mul_mem_right]))
      (add norm 0 (by grind only [Ideal.mem_colon_singleton]))
      (add norm 0 (by grind only [Ideal.span_singleton_mem_isPrincipalSubmonoid]))
      (add norm 0 (by grind only [Ideal.subset_span]))
      (add norm 0 (by grind only [Ideal.span]))
      (add norm 0 (by grind only [Ideal.mem_span_singleton_self]))
      (add norm 0 (by grind only [Ideal.pow_mem_pow]))
      (add norm 0 (by grind only [FractionalIdeal.coeIdeal_mul]))
      (add norm 0 (by grind only [ClassGroup.mk0_eq_mk0_inv_iff]))
      (add norm 0 (by grind only [conductor_mul_differentIdeal]))
      (add norm 0 (by grind only [Ideal.norm_mem_spanNorm]))
      (add norm 0 (by grind only [Ideal.mem_map_of_mem]))
      (add norm 0 (by grind only [ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring]))
      (add norm 0 (by grind only [Ideal.mem_span_singleton']))
      (add norm 0 (by grind only [FractionalIdeal.coeIdeal_span_singleton]))
      (add norm 0 (by grind only [Ideal.span_singleton_pow]))
      (add norm 0 (by grind only [pow_mem]))
      (add norm 0 (by grind only [Star]))
      (add norm 0 (by grind only [Ideal.mem_comap]))
      (add norm 0 (by grind only [FractionalIdeal.mul_mem_mul]))
      (add norm 0 (by grind only [Ideal.pow_le_pow_right]))
      (add norm 0 (by grind only [Ideal.mul_mono]))
      (add norm 0 (by grind only [Submodule.mul_mem_mul]))
      (add norm 0 (by grind only [Ideal.mul_homogeneous_element_mem_of_mem]))
      (add norm 0 (by grind only [Ideal.mul_top]))
      (add norm 0 (by grind only [FractionalIdeal.mem_coeIdeal_of_mem]))

  obtain ⟨z, hz_eq⟩ := h_z_in_I
  -- Step 6 & 9: The imaginary part of star w_val * w_val is 0
  have h_im_zero : (star w_val * w_val : GaussianInt).im = 0 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Zsqrtd.norm_def]))
      (add norm 0 (by grind only [Zsqrtd.mul_re]))
      (add norm 0 (by grind only [Zsqrtd.mul_im]))
      (add norm 0 (by grind only [Quaternion.im_re]))
      (add norm 0 (by grind only [RCLike.I_im]))
      (add norm 0 (by grind only [RCLike.mul_im]))
      (add norm 0 (by grind only [RCLike.mul_re]))
      (add norm 0 (by grind only [Quaternion.star_mul_eq_coe]))
      (add norm 0 (by grind only [Quaternion.re_add_im]))
      (add norm 0 (by grind only [RCLike.im_eq_conj_sub]))
      (add norm 0 (by grind only [RCLike.I_im']))
      (add norm 0 (by grind only [Quaternion.im]))
      (add norm 0 (by grind only [RCLike.conj_im]))
      (add norm 0 (by grind only [Complex.mul_im]))
      (add norm 0 (by grind only [Quaternion.mul_star_eq_coe]))
      (add norm 0 (by grind only [Quaternion.inner_def]))
      (add norm 0 (by grind only [QuaternionAlgebra.coe_imI]))
      (add norm 0 (by grind only [RCLike.re_add_im]))
      (add norm 0 (by grind only [QuaternionAlgebra.coe_im]))
      (add norm 0 (by grind only [Quaternion.mul_imK]))
      (add norm 0 (by grind only [Quaternion.im_star]))
      (add norm 0 (by grind only [Quaternion.coeComplex_imI]))
      (add norm 0 (by grind only [QuaternionAlgebra.im_imI]))
      (add norm 0 (by grind only [Quaternion.star_imI]))
      (add norm 0 (by grind only [RCLike.I_mul_re]))
      (add norm 0 (by grind only [Zsqrtd.add_im]))
      (add norm 0 (by grind only [UpperHalfPlane.im]))
      (add norm 0 (by grind only [Complex.mul_re]))
      (add norm 0 (by grind only [Quaternion.coe_im]))
      (add norm 0 (by grind only [Complex.add_im]))
      (add norm 0 (by grind only [UpperHalfPlane.re_add_im]))
      (add norm 0 (by grind only [Quaternion.eq_re_of_eq_coe]))

  -- Therefore, (z : GaussianInt).im = 0
  have h_z_im_zero : (z : GaussianInt).im = 0 := by
    clear * - hz_eq h_im_zero
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
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
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Zsqrtd.norm_def]))
      (add norm 0 (by grind only [Quaternion.im_re]))
      (add norm 0 (by grind only [Zsqrtd.mul_im]))
      (add norm 0 (by grind only [Zsqrtd.mul_re]))
      (add norm 0 (by grind only [RCLike.I_im]))
      (add norm 0 (by grind only [Complex.ofReal_im]))
      (add norm 0 (by grind only [Complex.mul_im]))
      (add norm 0 (by grind only [Quaternion.coe_im]))
      (add norm 0 (by grind only [QuaternionAlgebra.coe_im]))
      (add norm 0 (by grind only [Complex.add_im]))
      (add norm 0 (by grind only [RCLike.I_im']))
      (add norm 0 (by grind only [Complex.mul_re]))
      (add norm 0 (by grind only [Quaternion.coeComplex_imI]))
      (add norm 0 (by grind only [UpperHalfPlane.im]))
      (add norm 0 (by grind only [Quaternion.im]))
      (add norm 0 (by grind only [UpperHalfPlane.mk_im]))
      (add norm 0 (by grind only [Complex.re_add_im]))
      (add norm 0 (by grind only [inner_self_im]))
      (add norm 0 (by grind only [Quaternion.im_star]))
      (add norm 0 (by grind only [Zsqrtd.add_im]))
      (add norm 0 (by grind only [UpperHalfPlane.re_add_im]))
      (add norm 0 (by grind only [Quaternion.star_im]))
      (add norm 0 (by grind only [Complex.ext]))
      (add norm 0 (by grind only [RCLike.im_ofReal_mul]))
      (add norm 0 (by grind only [UpperHalfPlane.coe_im]))
      (add norm 0 (by grind only [Quaternion.coe_imI]))
      (add norm 0 (by grind only [Complex.I_im]))
      (add norm 0 (by grind only [QuaternionAlgebra.im_imI]))
      (add norm 0 (by grind only [QuaternionAlgebra.im_re]))
      (add norm 0 (by grind only [RCLike.im_eq_conj_sub]))
      (add norm 0 (by grind only [Complex.zero_im]))
      (add norm 0 (by grind only [RCLike.conj_im]))

  -- Step 7 & 8: Show that z ≠ 0
  -- z.val = star w_val * w_val = norm(w_val) as a GaussianInt with im=0
  -- norm(w_val) = a^2 + b^2 where w_val = a + bi
  -- Since w ≠ 0, not both a and b are zero, so a^2 + b^2 > 0
  have h_norm_pos : (star w_val * w_val : GaussianInt) ≠ 0 := by
    clear * - hw_ne_zero
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 520
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [RatFunc.algebraMap_ne_zero]))
      (add norm 0 (by grind only [RatFunc.num_ne_zero]))
      (add norm 0 (by grind only [ModP.mul_ne_zero_of_pow_p_ne_zero]))
      (add norm 0 (by grind only [mul_ne_zero_iff]))
      (add norm 0 (by grind only [FractionalIdeal.ideal_factor_ne_zero]))
      (add norm 0 (by grind only [RatFunc.coe_ne_zero]))
      (add norm 0 (by grind only [pow_ne_zero]))
      (add norm 0 (by grind only [RatFunc.denom_ne_zero]))
      (add norm 0 (by grind only [FractionalIdeal.coeIdeal_mul]))
      (add norm 0 (by grind only [map_ne_zero]))
      (add norm 0 (by grind only [mul_right_inj']))
      (add norm 0 (by grind only [inv_ne_zero]))
      (add norm 0 (by grind only [WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero]))
      (add norm 0 (by grind only [Polynomial.Monic.mul_left_ne_zero]))
      (add norm 0 (by grind only [FractionalIdeal.spanSingleton_ne_zero_iff]))
      (add norm 0 (by grind only [RatFunc.natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_const_iff]))
      (add norm 0 (by grind only [FractionalIdeal.constant_factor_ne_zero]))
      (add norm 0 (by grind only [WeierstrassCurve.Jacobian.X_eq_iff]))
      (add norm 0 (by grind only [RCLike.ofReal_ne_zero]))
      (add norm 0 (by grind only [Ideal.span_singleton_eq_bot]))
      (add norm 0 (by grind only [WeierstrassCurve.Jacobian.toAffine_negAddY_of_ne]))
      (add norm 0 (by grind only [RatFunc.num_mul_eq_mul_denom_iff]))
      (add norm 0 (by grind only [CstarRing.star_mul_self_ne_zero_iff]))
      (add norm 0 (by grind only [NumberField.Units.coe_ne_zero]))
      (add norm 0 (by grind only [ne_zero_of_mem_circle]))
      (add norm 0 (by grind only [FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction]))
      (add norm 0 (by grind only [div_eq_div_iff]))
      (add norm 0 (by grind only [WeierstrassCurve.Jacobian.toAffine_addX_of_ne]))
      (add norm 0 (by grind only [mul_left_cancel₀]))
      (add safe 0 (by simp only [mul_ne_zero] at *))
      (add safe 0 (by simp only [div_ne_zero] at *))

  have h_z_ne_zero : z ≠ 0 := by
    clear * - hz_eq h_norm_pos
    intro H
    apply h_norm_pos
    rw [← hz_eq, H, Submodule.coe_zero]

  -- Final conclusion
  refine' ⟨z, h_z_ne_zero, h_z_im_zero⟩
