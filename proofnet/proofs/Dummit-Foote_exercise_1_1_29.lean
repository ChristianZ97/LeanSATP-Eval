
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_1_1_29 {A B : Type*} [Group A] [Group B] :
  (∀ x y : A × B, x*y = y*x) ↔ (∀ x y : A, x*y = y*x) ∧
  (∀ x y : B, x*y = y*x) := by
  constructor
  · -- Forward direction: Commutativity in A × B implies commutativity in A and B
    intro h_comm_AB
    have h_comm_A : ∀ (a c : A), a * c = c * a := by
      intro a c
      let p : A × B := (a, 1)
      let q : A × B := (c, 1)
      have h1 : p * q = q * p := h_comm_AB p q
      simp at h1
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        maxGoals := 512
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
        (add safe 100 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 10% (by exfalso))
        (add unsafe 50% (by ring_nf at *))
        (add norm 0 (by grind only [mul_assoc]))
        (add norm 0 (by grind only [Prod.mk_mul_mk]))
        (add norm 0 (by grind only [Subgroup.IsComplement.equiv_fst_eq_mul_inv]))
        (add norm 0 (by grind only [Subgroup.IsComplement.equiv_snd_eq_inv_mul]))
        (add norm 0 (by grind only [Monoid.CoprodI.Word.equivPair_symm]))
        (add norm 0 (by grind only [mul_right_inj]))
        (add norm 0 (by grind only [mul_left_comm]))
        (add norm 0 (by grind only [Subgroup.coe_mul]))
        (add norm 0 (by grind only [HNNExtension.equiv_eq_conj]))
        (add norm 0 (by grind only [Subgroup.IsComplement.equiv_mul_left]))
        (add norm 0 (by grind only [Subgroup.IsComplement.equiv_fst_mul_equiv_snd]))
        (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
        (add norm 0 (by grind only [mul_left_inj]))
        (add norm 0 (by rw [mul_self]))
        (add norm 0 (by rw [mul_one]))
        (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isTwoCocycle]))
        (add norm 0 (by grind only [HNNExtension.equiv_symm_eq_conj]))
        (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isMulTwoCocycle]))
        (add norm 0 (by grind only [HNNExtension.NormalWord.prod_cons]))
        (add norm 0 (by grind only [mul_mul_mul_comm]))
        (add norm 0 (by grind only [commutatorElement_def]))
        (add norm 0 (by grind only [groupCohomology.twoCocycles_map_one_fst]))
        (add norm 0 (by grind only [Monoid.PushoutI.NormalWord.equivPair]))
        (add norm 0 (by grind only [Monoid.PushoutI.NormalWord.prod_cons]))
        (add norm 0 (by grind only [LaurentPolynomial.mul_T_assoc]))
        (add norm 0 (by rw [one_mul]))
        (add norm 0 (by grind only [Subgroup.IsComplement.equiv_mul_left_of_mem]))
        (add norm 0 (by grind only [mul_right_comm]))
        (add norm 0 (by grind only [CliffordAlgebraQuaternion.Q_apply]))
        (add norm 0 (by grind only [conj_mul]))
        (add norm 0 (by grind only [Monoid.PushoutI.NormalWord.summand_smul_def]))
        (add norm 0 (by grind only [Monoid.PushoutI.NormalWord.cons_eq_smul]))

    have h_comm_B : ∀ (b d : B), b * d = d * b := by
      intro b d
      let p : A × B := (1, b)
      let q : A × B := (1, d)
      have h1 : p * q = q * p := h_comm_AB p q
      simp at h1
      aesop (config := {
        maxRuleApplications := 40
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        maxGoals := 512
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 100 (by gcongr))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 10% (by exfalso))
        (add unsafe 50% (by ring_nf at *))
        (add norm 0 (by grind only [Prod.mk_mul_mk]))
        (add norm 0 (by rw [mul_one]))
        (add norm 0 (by rw [one_mul]))
        (add norm 0 (by grind only [mul_right_inj]))
        (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isTwoCocycle]))
        (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isMulTwoCocycle]))
        (add norm 0 (by grind only [mul_self]))
        (add norm 0 (by grind only [mul_left_inj]))
        (add norm 0 (by grind only [mul_assoc]))
        (add norm 0 (by grind only [groupCohomology.twoCocycles_map_one_fst]))
        (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
        (add norm 0 (by grind only [Prod.fst_mul]))
        (add norm 0 (by grind only [groupCohomology.map_one_snd_of_isTwoCocycle]))
        (add norm 0 (by grind only [Subgroup.IsComplement.equiv_fst_eq_mul_inv]))
        (add norm 0 (by grind only [DualNumber.snd_eps]))
        (add norm 0 (by grind only [groupCohomology.twoCocycles_map_one_snd]))
        (add norm 0 (by grind only [groupCohomology.map_one_snd_of_isMulTwoCocycle]))
        (add norm 0 (by grind only [LaurentPolynomial.mul_T_assoc]))
        (add norm 0 (by grind only [Monoid.CoprodI.Word.equivPair_symm]))
        (add norm 0 (by grind only [commutatorElement_def]))
        (add norm 0 (by grind only [Subgroup.coe_mul]))
        (add norm 0 (by grind only [add_self]))
        (add norm 0 (by grind only [mul_inv_self]))
        (add norm 0 (by grind only [Subgroup.IsComplement.equiv_snd_eq_inv_mul]))
        (add norm 0 (by grind only [HNNExtension.equiv_eq_conj]))
        (add norm 0 (by grind only [Subgroup.IsComplement.equiv_fst_mul_equiv_snd]))
        (add norm 0 (by grind only [CliffordAlgebra.ofProd_ι_mk]))
        (add norm 0 (by grind only [AlgebraicGeometry.Proj.mul_apply]))
        (add norm 0 (by grind only [Unitization.fst_inl]))
        (add norm 0 (by grind only [Prod.snd_mul]))
        (add norm 0 (by grind only [Prod.ext]))
        (add norm 0 (by grind only [LaurentPolynomial.T_add]))

    exact ⟨h_comm_A, h_comm_B⟩

  · -- Reverse direction: Commutativity in A and B implies commutativity in A × B
    rintro ⟨h_comm_A, h_comm_B⟩
    intro x y
    have h_xy : x * y = y * x := by
      cases x with | mk a b =>
      cases y with | mk c d =>
        simp only [Prod.ext_iff]
        constructor
        · show a * c = c * a
          exact h_comm_A a c

        · show b * d = d * b
          exact h_comm_B b d

    exact h_xy
