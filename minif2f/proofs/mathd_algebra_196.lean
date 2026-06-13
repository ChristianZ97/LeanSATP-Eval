import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    (∑ k in S, k) = 4 := by
  have h_abs_prop : ∀ x : ℝ, abs ((2:ℝ) - x) = 3 ↔ (2:ℝ) - x = 3 ∨ (2:ℝ) - x = (-3:ℝ) := by
    clear * -
    rintro a <;> simp [abs_eq]

  have h_case1_equiv : ∀ x : ℝ, (2:ℝ) - x = 3 ↔ x = (-1:ℝ) := by
    clear * -
    aesop
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_num [*] at *))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply AffineSubspace.left_mem_perpBisector | rw [AffineSubspace.left_mem_perpBisector] | simp only [AffineSubspace.left_mem_perpBisector]))
    (add unsafe 30% (by first | apply AffineSubspace.right_mem_perpBisector | rw [AffineSubspace.right_mem_perpBisector] | simp only [AffineSubspace.right_mem_perpBisector]))
    (add unsafe 30% (by first | apply Real.Angle.toReal_eq_pi_div_two_iff | rw [Real.Angle.toReal_eq_pi_div_two_iff] | simp only [Real.Angle.toReal_eq_pi_div_two_iff]))
    (add unsafe 30% (by first | apply Real.Angle.toReal_eq_pi_iff | rw [Real.Angle.toReal_eq_pi_iff] | simp only [Real.Angle.toReal_eq_pi_iff]))
    (add unsafe 30% (by first | apply Real.Angle.toReal_inj | rw [Real.Angle.toReal_inj] | simp only [Real.Angle.toReal_inj]))
    (add unsafe 10% (by first | apply NumberField.RingOfIntegers.eq_iff | rw [NumberField.RingOfIntegers.eq_iff] | simp only [NumberField.RingOfIntegers.eq_iff]))
    (add unsafe 10% (by first | apply PMF.ext_iff | rw [PMF.ext_iff] | simp only [PMF.ext_iff]))

  have h_case2_equiv : ∀ x : ℝ, (2:ℝ) - x = (-3:ℝ) ↔ x = (5:ℝ) := by
    clear * -
    intro x
    apply Iff.intro
    · intro a
      (nlinarith)
    · intro a
      subst a
      (nlinarith)

  have h_member_iff : ∀ x : ℝ, x ∈ S ↔ x = (-1:ℝ) ∨ x = (5:ℝ) := by
    clear * - h₀ h_abs_prop h_case1_equiv h_case2_equiv
    intro x
    simp_all only

  have h_neg1_root : abs ((2:ℝ) - (-1:ℝ)) = 3 := by
    clear * -
    simp_all only [sub_neg_eq_add]
    (ring_nf)
    simp_all only [abs_ofNat]

  have h_neg1_in_S : (-1:ℝ) ∈ S := by
    clear * - h₀ h_neg1_root
    simp_all only [sub_neg_eq_add]

  have h_5_root : abs ((2:ℝ) - (5:ℝ)) = 3 := by
    clear * -
    (ring_nf)
    simp_all only [abs_neg, abs_ofNat]

  have h_5_in_S : (5:ℝ) ∈ S := by
    clear * - h₀ h_5_root
    simp_all only

  have h_S_is_finite_set : S = {(-1:ℝ), (5:ℝ)} := by
    clear * - h_member_iff h_neg1_in_S h_5_in_S
    simp_all only [true_or, or_true]
    ext a : 1
    simp_all only [Finset.mem_insert, Finset.mem_singleton]

  have h_sum_substitution : (∑ k in S, k) = (∑ k in {(-1:ℝ), (5:ℝ)}, k) := by
    clear * - h_S_is_finite_set
    subst h_S_is_finite_set
    simp_all only

  have h_sum_expansion : (∑ k in {(-1:ℝ), (5:ℝ)}, k) = ((-1:ℝ) + (5:ℝ)) := by
    clear * -
    repeat erw [Finset.sum_insert] <;> simp
    norm_num

  have h_final_addition : ((-1:ℝ) + (5:ℝ)) = 4 := by
    clear * -
    (ring)

  have h_final_result : (∑ k in S, k) = 4 := by
    clear * - h_sum_substitution h_sum_expansion h_final_addition
    simp_all only

  exact h_final_result
