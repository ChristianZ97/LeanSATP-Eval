
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_3_1_22a (G : Type*) [Group G] (H K : Subgroup G)
  [Normal H] [Normal K] :
  Normal (H ⊓ K) := by
  -- Step 1: Define the conjugate set for an element in H ∩ K
  let conj_set := fun (g : G) => { y : G | ∃ x ∈ H ⊓ K, y = g * x * g⁻¹ }
  -- Step 2: If x is in H ∩ K, then x is in H
  have h_in_H : ∀ (x : G), x ∈ H ⊓ K → x ∈ H := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [and_imp]))
      (add norm 0 (by grind only [imp_forall_iff]))
      (add norm 0 (by grind only [Subgroup.mem_inf]))
      (add norm 0 (by grind only [iff_self_iff]))
      (add norm 0 (by grind only [Prod.forall]))
      (add norm 0 (by grind only [exists_imp]))
      (add norm 0 (by grind only [SimpleGraph.Subgraph.verts_inf]))
      (add norm 0 (by grind only [Pi.inf_apply]))
      (add norm 0 (by grind only [forall_swap]))
      (add norm 0 (by grind only [le_inf_iff]))
      (add norm 0 (by grind only [Finset.le_inf_iff]))
      (add norm 0 (by grind only [forall_const]))
      (add norm 0 (by grind only [Pi.le_def]))
      (add norm 0 (by grind only [BoxIntegral.Box.mem_def]))
      (add norm 0 (by grind only [Subtype.forall]))
      (add norm 0 (by grind only [forall_exists_index]))
      (add norm 0 (by grind only [OmegaCompletePartialOrder.ωSup_le_iff]))
      (add norm 0 (by grind only [Finset.le_inf'_iff]))
      (add norm 0 (by grind only [CategoryTheory.Sieve.inter_apply]))
      (add norm 0 (by grind only [forall_and]))
      (add norm 0 (by grind only [YoungDiagram.mem_inf]))
      (add norm 0 (by grind only [Set.le_einfsep_iff]))
      (add norm 0 (by grind only [forall_apply_eq_imp_iff₂]))
      (add norm 0 (by grind only [Order.PFilter.inf_mem_iff]))
      (add norm 0 (by grind only [NonemptyInterval.mem_def]))
      (add norm 0 (by grind only [IntermediateField.mem_inf]))
      (add norm 0 (by grind only [Order.Ideal.mem_inf]))
      (add norm 0 (by grind only [Set.subset_def]))
      (add norm 0 (by grind only [CategoryTheory.GrothendieckTopology.intersection_covering_iff]))
      (add norm 0 (by grind only [FirstOrder.Language.Formula.realize_inf]))
      (add norm 0 (by grind only [Set.setOf_subset_setOf]))
      (add norm 0 (by grind only [ConvexCone.mem_inf]))

  -- Step 3: Since H is normal, for any g ∈ G and x ∈ H, gxg⁻¹ ∈ H
  have h_H_normal : ∀ (g : G) (x : G), x ∈ H → g * x * g⁻¹ ∈ H := by
    clear * -
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Subgroup.MemLeftTransversals.inv_mul_toFun_mem]))
      (add norm 0 (by grind only [commutatorElement_def]))
      (add norm 0 (by grind only [Subgroup.Normal.mem_comm_iff]))
      (add norm 0 (by grind only [mul_inv_cancel_left]))
      (add norm 0 (by grind only [MulAut.conj]))
      (add norm 0 (by grind only [mul_mem_cancel_left]))
      (add norm 0 (by grind only [mul_inv_self]))
      (add norm 0 (by grind only [Subgroup.commutator_mem_commutator]))
      (add norm 0 (by grind only [MulAut.conj_inv_apply]))
      (add norm 0 (by grind only [MulAut.conj_symm_apply]))
      (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add norm 0 (by grind only [Subgroup.MemRightTransversals.mul_inv_toFun_mem]))
      (add norm 0 (by grind only [inv_mul_cancel_left]))
      (add norm 0 (by grind only [MulAut.conj_apply]))
      (add norm 0 (by grind only [Subgroup.MemLeftTransversals.inv_toFun_mul_mem]))
      (add norm 0 (by grind only [Subgroup.inv_mem_iff]))
      (add norm 0 (by grind only [mul_inv_eq_iff_eq_mul]))
      (add norm 0 (by grind only [mul_mem_cancel_right]))
      (add norm 0 (by grind only [derivedSeries_normal]))
      (add norm 0 (by grind only [Equiv.Perm.sameCycle_conj]))
      (add norm 0 (by grind only [IsSubgroup.mul_mem_cancel_left]))
      (add norm 0 (by grind only [Subgroup.MemRightTransversals.toFun_mul_inv_mem]))
      (add norm 0 (by grind only [TopologicalGroup.continuous_conj]))
      (add norm 0 (by grind only [eq_inv_mul_iff_mul_eq]))
      (add norm 0 (by grind only [mul_inv_cancel_right]))
      (add norm 0 (by grind only [InvMemClass]))
      (add norm 0 (by grind only [Subgroup.mem_top]))
      (add norm 0 (by grind only [ExistsUnique.unique]))
      (add norm 0 (by grind only [Subgroup.Normal]))
      (add norm 0 (by grind only [CategoryTheory.PresheafOfGroups.Cochain₀.inv_apply]))
      (add norm 0 (by grind only [Subgroup.mem_map_of_mem]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))

  -- Step 4: If x is in H ∩ K, then x is in K
  have h_in_K : ∀ (x : G), x ∈ H ⊓ K → x ∈ K := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [and_imp]))
      (add norm 0 (by grind only [Subgroup.mem_inf]))
      (add norm 0 (by grind only [imp_forall_iff]))
      (add norm 0 (by grind only [exists_imp]))
      (add norm 0 (by grind only [Prod.forall]))
      (add norm 0 (by grind only [iff_self_iff]))
      (add norm 0 (by grind only [forall_exists_index]))
      (add norm 0 (by grind only [forall_apply_eq_imp_iff₂]))
      (add norm 0 (by grind only [forall_const]))
      (add norm 0 (by grind only [Pi.inf_apply]))
      (add norm 0 (by grind only [SimpleGraph.Subgraph.verts_inf]))
      (add norm 0 (by grind only [Subtype.forall]))
      (add norm 0 (by grind only [le_inf_iff]))
      (add norm 0 (by grind only [Finset.le_inf_iff]))
      (add norm 0 (by grind only [IntermediateField.mem_inf]))
      (add norm 0 (by grind only [Finset.le_inf'_iff]))
      (add norm 0 (by grind only [forall_swap]))
      (add norm 0 (by grind only [Pi.le_def]))
      (add norm 0 (by grind only [YoungDiagram.mem_inf]))
      (add norm 0 (by grind only [Subgroup.mem_comap]))
      (add norm 0 (by grind only [BoxIntegral.Box.mem_def]))
      (add norm 0 (by grind only [Order.Ideal.mem_inf]))
      (add norm 0 (by grind only [OmegaCompletePartialOrder.ωSup_le_iff]))
      (add norm 0 (by grind only [Subgroup.mem_normalizer_iff]))
      (add norm 0 (by grind only [CategoryTheory.Sieve.inter_apply]))
      (add norm 0 (by grind only [CategoryTheory.GrothendieckTopology.intersection_covering_iff]))
      (add norm 0 (by grind only [TopologicalSpace.Compacts.coe_inf]))
      (add norm 0 (by grind only [LieSubalgebra.mem_inf]))
      (add norm 0 (by grind only [Set.le_einfsep_iff]))
      (add norm 0 (by grind only [Order.PFilter.inf_mem_iff]))
      (add norm 0 (by grind only [implies_true]))
      (add norm 0 (by grind only [FirstOrder.Language.BoundedFormula.realize_iInf]))

  -- Step 5: Since K is normal, for any g ∈ G and x ∈ K, gxg⁻¹ ∈ K
  have h_K_normal : ∀ (g : G) (x : G), x ∈ K → g * x * g⁻¹ ∈ K := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Subgroup.MemLeftTransversals.inv_mul_toFun_mem]))
      (add norm 0 (by grind only [Subgroup.Normal.mem_comm_iff]))
      (add norm 0 (by grind only [commutatorElement_def]))
      (add norm 0 (by grind only [mul_mem_cancel_left]))
      (add norm 0 (by grind only [MulAut.conj]))
      (add norm 0 (by grind only [Subgroup.commutator_mem_commutator]))
      (add norm 0 (by grind only [Subgroup.MemRightTransversals.mul_inv_toFun_mem]))
      (add norm 0 (by grind only [mul_inv_cancel_left]))
      (add norm 0 (by grind only [MulAut.conj_inv_apply]))
      (add norm 0 (by grind only [Subgroup.inv_mem_iff]))
      (add norm 0 (by grind only [MulAut.conj_symm_apply]))
      (add norm 0 (by grind only [Subgroup.MemLeftTransversals.inv_toFun_mul_mem]))
      (add norm 0 (by grind only [mul_inv_self]))
      (add norm 0 (by grind only [mul_mem_cancel_right]))
      (add norm 0 (by grind only [MulAut.conj_apply]))
      (add norm 0 (by grind only [derivedSeries_normal]))
      (add norm 0 (by grind only [IsSubgroup.mul_mem_cancel_left]))
      (add norm 0 (by grind only [groupCohomology.oneCocycles_map_mul_of_isTrivial]))
      (add norm 0 (by grind only [inv_mul_cancel_left]))
      (add norm 0 (by grind only [InvMemClass]))
      (add norm 0 (by grind only [Subgroup.mem_top]))
      (add norm 0 (by grind only [Subgroup.MemRightTransversals.toFun_mul_inv_mem]))
      (add norm 0 (by grind only [mul_inv_eq_iff_eq_mul]))
      (add norm 0 (by grind only [Equiv.Perm.sameCycle_conj]))
      (add norm 0 (by grind only [TopologicalGroup.continuous_conj]))
      (add norm 0 (by grind only [Subgroup.Normal]))
      (add norm 0 (by grind only [ExistsUnique.unique]))
      (add norm 0 (by grind only [Subgroup.mem_map_of_mem]))
      (add norm 0 (by grind only [IsSubgroup.inv_mem_iff]))
      (add norm 0 (by grind only [Subgroup.mem_leftTransversals_iff_existsUnique_inv_mul_mem]))
      (add norm 0 (by grind only [Subgroup.isComplement_iff_existsUnique]))
      (add unsafe 50% (by nlinarith [mul_inv_eq_one]))

  -- Step 6: For any g ∈ G and x ∈ H ∩ K, gxg⁻¹ is in both H and K, hence in H ∩ K
  have h_conj_in_intersect : ∀ (g : G) (x : G), x ∈ H ⊓ K → g * x * g⁻¹ ∈ H ⊓ K := by
    clear * - h_in_H h_H_normal h_in_K h_K_normal
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
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
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Subgroup.mem_inf]))
      (add norm 0 (by grind only [le_inf_iff]))
      (add norm 0 (by grind only [Subgroup.commutator_mem_commutator]))
      (add norm 0 (by grind only [Subgroup.Normal.mem_comm_iff]))
      (add norm 0 (by grind only [Subgroup.inv_mem_iff]))
      (add norm 0 (by grind only [InvMemClass]))
      (add norm 0 (by grind only [Subgroup.mem_normalizer_iff]))
      (add norm 0 (by grind only [HomogeneousIdeal.coe_inf]))
      (add norm 0 (by grind only [TopologicalSpace.Compacts.coe_inf]))
      (add norm 0 (by grind only [Subgroup.mem_top]))
      (add norm 0 (by grind only [Subgroup.MemLeftTransversals.inv_mul_toFun_mem]))
      (add norm 0 (by grind only [IsSubgroup.inv_mem_iff]))
      (add norm 0 (by grind only [Subgroup.mem_map_of_mem]))
      (add norm 0 (by grind only [CategoryTheory.GrothendieckTopology.intersection_covering_iff]))
      (add norm 0 (by grind only [Subgroup.MemRightTransversals.mul_inv_toFun_mem]))
      (add norm 0 (by grind only [inf_mul]))
      (add norm 0 (by grind only [mul_mem_cancel_left]))
      (add norm 0 (by grind only [commutatorElement_def]))
      (add norm 0 (by grind only [derivedSeries_normal]))
      (add norm 0 (by grind only [Subgroup.MemLeftTransversals.inv_toFun_mul_mem]))
      (add norm 0 (by grind only [Subgroup.mem_comap]))
      (add norm 0 (by grind only [Subgroup.Normal]))
      (add norm 0 (by grind only [MulAut.conj]))
      (add norm 0 (by grind only [MulAction.mem_stabilizer_set]))
      (add norm 0 (by grind only [MulAction.mem_stabilizer_finset]))
      (add norm 0 (by grind only [IntermediateField.mem_inf]))
      (add norm 0 (by grind only [IsSubgroup.mul_mem_cancel_left]))
      (add norm 0 (by grind only [TopologicalSpace.Closeds.coe_inf]))
      (add norm 0 (by grind only [Subgroup.MemRightTransversals.toFun_mul_inv_mem]))
      (add norm 0 (by grind only [IntermediateField.mem_fixingSubgroup_iff]))
      (add norm 0 (by grind only [mul_mem_cancel_right]))
      (add norm 0 (by grind only [HomogeneousIdeal.toIdeal_inf]))

  -- Step 7: The set of conjugates {gxg⁻¹ | x ∈ H ∩ K} is a subset of H ∩ K
  have h_subset : ∀ (g : G), conj_set g ⊆ (H ⊓ K : Set G) := by
    clear * - h_conj_in_intersect
    intro g x hx_in_HK
    rcases hx_in_HK with ⟨y, ⟨hy_in_H, hy_in_K⟩, rfl⟩
    exact h_conj_in_intersect g y ⟨hy_in_H, hy_in_K⟩

  -- Step 8: For all g ∈ G, g(H ∩ K)g⁻¹ ⊆ H ∩ K
  -- have h_normal_condition : ∀ (g : G), (H ⊓ K).conjugate g ≤ (H ⊓ K) := by
    -- -- Note: In Lean, subgroup conjugation and subset relations are handled via .conjugate and ≤
    -- -- We need to bridge the set-level statement with the subgroup structure.
    -- -- A direct way is to show that for any y in conjugate of (H⊓K) by g, y is in (H⊓K).
    -- intros g y hy
    -- have h_mem_conj : y ∈ (conj_set g : Set G) := by
      -- -- By definition of conjugate subgroup in terms of sets
      -- sorry

    -- have h_y_in : y ∈ (H ⊓ K : Set G) := by
      -- have h_sub := h_subset g
      -- exact h_sub h_mem_conj

    -- exact h_y_in

  -- Step 9: Therefore, H ∩ K is normal in G
  have h_normal : Normal (H ⊓ K) := by
    -- Use the criterion that if for all g, g(H∩K)g⁻¹ <= H∩K, then it's normal
    -- Lean's Normal class might require showing this directly or using existing lemmas.
    refine { conj_mem := ?conj_mem }
    intro n n_in_HK g
    exact h_conj_in_intersect g n n_in_HK

  exact h_normal
