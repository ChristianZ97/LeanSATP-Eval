
import Mathlib

open Filter Real Function
open scoped Topology


set_option maxHeartbeats 0

theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  -- Step 1: IsOpen U ↔ U = interior U
  have h1 : IsOpen U ↔ U = interior U := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 600
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [interior_eq_iff_isOpen]))
      (add norm 0 (by grind only [exterior_subset_iff_isOpen]))
      (add norm 0 (by grind only [subset_interior_iff_isOpen]))
      (add norm 0 (by grind only [IsOpen.interior_eq]))
      (add norm 0 (by grind only [exterior_def]))
      (add norm 0 (by grind only [isOpen_exterior]))
      (add norm 0 (by grind only [isOpen_interior]))
      (add norm 0 (by grind only [exterior_eq_iff_isOpen]))
      (add norm 0 (by grind only [interior_interior]))
      (add norm 0 (by grind only [exterior]))
      (add norm 0 (by grind only [IsOpen.subset_interior_iff]))
      (add norm 0 (by grind only [IsOpen.exterior_subset_iff]))
      (add norm 0 (by grind only [IsOpenMap.preimage_interior_eq_interior_preimage]))
      (add norm 0 (by grind only [subset_interior_iff_nhds]))
      (add norm 0 (by grind only [Subgroup.isOpen_of_one_mem_interior]))
      (add norm 0 (by grind only [IsOpen.exterior_subset]))
      (add norm 0 (by grind only [interior_inter]))
      (add norm 0 (by grind only [mem_exterior]))
      (add norm 0 (by grind only [TopologicalSpace.Opens.interior]))
      (add norm 0 (by grind only [mem_interior]))
      (add norm 0 (by grind only [exterior_exterior]))
      (add norm 0 (by grind only [interior]))
      (add norm 0 (by grind only [ContinuousLinearMap.interior_preimage]))
      (add norm 0 (by grind only [mem_interior_iff_mem_nhds]))
      (add norm 0 (by grind only [ModelWithCorners.IsInteriorPoint]))
      (add norm 0 (by grind only [Convex.interior]))
      (add norm 0 (by grind only [interior_mono]))
      (add norm 0 (by grind only [PartialHomeomorph.preimage_interior]))
      (add norm 0 (by grind only [interior_maximal]))
      (add norm 0 (by grind only [interior_mem_nhds]))
      (add norm 0 (by grind only [preimage_interior_subset_interior_preimage]))
      (add norm 0 (by grind only [interior_smul]))

  -- Step 2: U = interior U ↔ ∀ x ∈ U, x ∈ interior U
  have h2 : U = interior U ↔ ∀ x ∈ U, x ∈ interior U := by
    clear * -
    constructor
    · intro h x hx
      rwa [← h]
    · intro h
      ext x
      constructor
      · exact h x
      · intro hx
        exact interior_subset hx

  -- Step 3: x ∈ interior U ↔ x ∉ closure (Uᶜ)
  have h3 : ∀ x : M, x ∈ interior U ↔ x ∉ closure (Uᶜ) := by
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
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by positivity))
      (add norm 0 (by grind only [interior_compl]))
      (add norm 0 (by grind only [closure_compl]))
      (add norm 0 (by grind only [closure_eq_compl_interior_compl]))
      (add norm 0 (by grind only [not_imp_comm]))
      (add norm 0 (by grind only [subset_interior_iff_nhds]))
      (add norm 0 (by grind only [Set.mem_compl_iff]))
      (add norm 0 (by grind only [mem_interior_iff_mem_nhds]))
      (add norm 0 (by grind only [interior_subset_closure]))
      (add norm 0 (by grind only [ContinuousMap.mem_idealOfSet]))
      (add norm 0 (by grind only [Set.compl_subset_compl]))
      (add norm 0 (by grind only [iff_self_iff]))
      (add norm 0 (by grind only [Set.mem_compl]))
      (add norm 0 (by grind only [not_imp_not]))
      (add norm 0 (by grind only [Set.compl_def]))
      (add norm 0 (by grind only [Set.subset_def]))
      (add norm 0 (by grind only [MeasureTheory.mem_fundamentalInterior]))
      (add norm 0 (by grind only [exterior]))
      (add norm 0 (by grind only [closure]))
      (add norm 0 (by grind only [Filter.mem_closure]))
      (add norm 0 (by grind only [tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn]))
      (add norm 0 (by grind only [mem_exterior]))
      (add norm 0 (by grind only [tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn]))
      (add norm 0 (by grind only [interior_mem_nhds]))
      (add norm 0 (by grind only [exterior_subset_iff_mem_nhdsSet]))
      (add norm 0 (by grind only [mem_interior]))
      (add norm 0 (by grind only [exterior_def]))
      (add norm 0 (by grind only [Set.ext_iff]))
      (add norm 0 (by grind only [forall_and]))
      (add norm 0 (by grind only [subset_interior_iff_mem_nhdsSet]))
      (add norm 0 (by grind only [imp_iff_not_or]))
      (add norm 0 (by grind only [interior_eq_nhds]))
      (add norm 0 (by grind only [IsClosed.isNowhereDense_iff]))

  -- Step 4: ∀ x ∈ U, x ∈ interior U ↔ ∀ x ∈ U, x ∉ closure (Uᶜ)
  have h4 : (∀ x ∈ U, x ∈ interior U) ↔ (∀ x ∈ U, x ∉ closure (Uᶜ)) := by
    clear * - h3
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
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [forall_congr']))
      (add norm 0 (by grind only [forall_swap]))
      (add norm 0 (by grind only [forall₂_congr]))
      (add norm 0 (by grind only [forall₄_congr]))
      (add norm 0 (by grind only [forall₂_swap]))
      (add norm 0 (by grind only [Iff.trans]))
      (add norm 0 (by grind only [forall₅_congr]))
      (add norm 0 (by grind only [forall_and]))
      (add norm 0 (by grind only [iff_assoc]))
      (add norm 0 (by grind only [iff_def]))
      (add norm 0 (by grind only [forall_comm]))
      (add norm 0 (by grind only [Subtype.forall']))
      (add norm 0 (by grind only [not_imp_comm]))
      (add norm 0 (by grind only [imp_forall_iff]))
      (add norm 0 (by grind only [subset_interior_iff_nhds]))
      (add norm 0 (by grind only [forall₃_congr]))
      (add norm 0 (by grind only [forall_cond_comm]))
      (add norm 0 (by grind only [Equiv.forall_congr]))
      (add norm 0 (by grind only [SetCoe.forall']))
      (add norm 0 (by grind only [Equiv.Perm.inv_aux]))
      (add norm 0 (by grind only [interior_compl]))
      (add norm 0 (by grind only [Iff.comm]))
      (add norm 0 (by grind only [Iff.rfl]))
      (add norm 0 (by grind only [mem_reesAlgebra_iff]))
      (add norm 0 (by grind only [Filter.Eventually]))
      (add norm 0 (by grind only [SetCoe.forall]))
      (add norm 0 (by grind only [Subtype.forall]))
      (add norm 0 (by grind only [and_congr]))
      (add norm 0 (by grind only [Iff.symm]))
      (add norm 0 (by grind only [closure_compl]))
      (add norm 0 (by grind only [Prod.forall]))
      (add norm 0 (by grind only [TopologicalSpace.noetherianSpace_iff_opens]))

  -- Step 5: ClusterPt x (𝓟 A) ↔ ∀ S ∈ 𝓟 A, x ∈ closure S
  -- Note: By definition, ClusterPt x F ↔ x ∈ ⋂₀ (F : Set (Set M)) where the intersection is over closures? 
  -- Actually, in Mathlib, ClusterPt x F means every neighborhood of x intersects every set in F.
  -- For F = 𝓟 A (the principal filter generated by A), this means ∀ S ⊇ A, x ∈ closure S? 
  -- Let's look at the informal proof steps 5-8 which derive: ClusterPt x (𝓟 A) ↔ x ∈ closure A.

  -- Step 6-7-8 combined: ClusterPt x (𝓟 A) ↔ x ∈ closure A
  have h8 : ∀ (x : M) (A : Set M), ClusterPt x (𝓟 A) ↔ x ∈ closure A := by
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
      (add norm 1 (by push_neg))
      (add norm 100 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mem_closure_iff_clusterPt]))
      (add norm 0 (by grind only [ClusterPt]))
      (add norm 0 (by grind only [closure_eq_cluster_pts]))
      (add norm 0 (by grind only [MapClusterPt]))
      (add norm 0 (by grind only [IsClosedMap.mapClusterPt_iff_lift'_closure]))
      (add norm 0 (by grind only [clusterPt_iff_forall_mem_closure]))
      (add norm 0 (by grind only [isClosed_iff_clusterPt]))
      (add norm 0 (by grind only [Ultrafilter.clusterPt_iff]))
      (add norm 0 (by grind only [Filter.le_principal_iff]))
      (add norm 0 (by grind only [mapClusterPt_iff_ultrafilter]))
      (add norm 0 (by grind only [Filter.exists_ultrafilter_iff]))
      (add norm 0 (by grind only [Cauchy]))
      (add norm 0 (by grind only [Filter.map_neBot_iff]))
      (add norm 0 (by grind only [Ultrafilter.inf_neBot_iff]))
      (add norm 0 (by grind only [Filter.le_def]))
      (add norm 0 (by grind only [clusterPt_iff_ultrafilter]))
      (add norm 0 (by grind only [mem_closure_iff_nhdsWithin_neBot]))
      (add norm 0 (by grind only [Filter.NeBot.mono]))
      (add norm 0 (by grind only [Filter.tendsto_iff_comap]))
      (add norm 0 (by grind only [clusterPt_iff_lift'_closure']))
      (add norm 0 (by grind only [mapClusterPt_def]))
      (add norm 0 (by grind only [mapClusterPt_iff]))
      (add norm 0 (by grind only [Filter.map_principal]))
      (add norm 0 (by grind only [Filter.neBot_of_le]))
      (add norm 0 (by grind only [BoxIntegral.IntegrationParams.toFilter_inf_iUnion_eq]))
      (add norm 0 (by grind only [Filter.HasBasis.le_iff]))
      (add norm 0 (by grind only [clusterPt_principal_iff]))
      (add norm 0 (by grind only [isClosedMap_iff_clusterPt]))
      (add norm 0 (by grind only [Filter.inf_principal_neBot_iff]))
      (add norm 0 (by grind only [clusterPt_iff_lift'_closure]))
      (add norm 0 (by grind only [CauchyFilter]))
      (add norm 0 (by grind only [clusterPt_iff_not_disjoint]))

  -- Step 9: ¬ClusterPt x (𝓟 Uᶜ) ↔ x ∉ closure (Uᶜ)
  have h9 : ∀ x : M, ¬ClusterPt x (𝓟 Uᶜ) ↔ x ∉ closure (Uᶜ) := by
    clear * - h8
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
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by positivity))
      (add norm 0 (by grind only [not_imp_not]))
      (add norm 0 (by grind only [Classical.not_forall]))
      (add norm 0 (by grind only [Classical.not_not]))
      (add norm 0 (by grind only [not_and]))
      (add norm 0 (by grind only [Set.mem_compl_iff]))
      (add norm 0 (by grind only [Set.compl_def]))
      (add norm 0 (by grind only [not_imp_comm]))
      (add norm 0 (by grind only [Filter.mem_closure]))
      (add norm 0 (by grind only [not_exists]))
      (add norm 0 (by grind only [mem_closure_iff_clusterPt]))
      (add norm 0 (by grind only [not_iff_not]))
      (add norm 0 (by grind only [Filter.neBot_iff]))
      (add norm 0 (by grind only [not_ne_iff]))
      (add norm 0 (by grind only [Set.not_not_mem]))
      (add norm 0 (by grind only [Filter.Frequently]))
      (add norm 0 (by grind only [imp_iff_not_or]))
      (add norm 0 (by grind only [clusterPt_iff_not_disjoint]))
      (add norm 0 (by grind only [ClusterPt]))
      (add norm 0 (by grind only [Matroid.indep_iff_not_dep]))
      (add norm 0 (by grind only [closure_eq_cluster_pts]))
      (add norm 0 (by grind only [iff_false_iff]))
      (add norm 0 (by grind only [not_iff_comm]))
      (add norm 0 (by grind only [mem_closure_iff_nhdsWithin_neBot]))
      (add norm 0 (by grind only [Filter.not_frequently]))
      (add norm 0 (by grind only [Filter.not_eventually]))
      (add norm 0 (by grind only [mapClusterPt_iff]))
      (add norm 0 (by grind only [isClosed_iff_clusterPt]))
      (add norm 0 (by grind only [not_iff]))
      (add norm 0 (by grind only [iff_self_iff]))
      (add norm 0 (by grind only [Ultrafilter.disjoint_iff_not_le]))
      (add norm 0 (by grind only [Set.compl_setOf]))
      (add norm 0 (by grind only [Matroid.dep_iff]))

  -- Step 10: ∀ x ∈ U, x ∉ closure (Uᶜ) ↔ ∀ x ∈ U, ¬ClusterPt x (𝓟 Uᶜ)
  have h10 : (∀ x ∈ U, x ∉ closure (Uᶜ)) ↔ (∀ x ∈ U, ¬ClusterPt x (𝓟 Uᶜ)) := by
    clear * - h9
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
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [not_imp_comm]))
      (add norm 0 (by grind only [not_imp_not]))
      (add norm 0 (by grind only [forall_swap]))
      (add norm 0 (by grind only [mem_closure_iff_clusterPt]))
      (add norm 0 (by grind only [Filter.mem_closure]))
      (add norm 0 (by grind only [Filter.Eventually]))
      (add norm 0 (by grind only [isClosed_iff_clusterPt]))
      (add norm 0 (by grind only [ClusterPt]))
      (add norm 0 (by grind only [imp_iff_not_or]))
      (add norm 0 (by grind only [clusterPt_iff_not_disjoint]))
      (add norm 0 (by grind only [Filter.neBot_iff]))
      (add norm 0 (by grind only [Filter.le_def]))
      (add norm 0 (by grind only [closure_eq_cluster_pts]))
      (add norm 0 (by grind only [forall_congr']))
      (add norm 0 (by grind only [Set.compl_def]))
      (add norm 0 (by grind only [Classical.not_forall]))
      (add norm 0 (by grind only [isPreirreducible_iff_closed_union_closed]))
      (add norm 0 (by grind only [mem_closure_iff_nhdsWithin_neBot]))
      (add norm 0 (by grind only [Set.subset_def]))
      (add norm 0 (by grind only [Filter.Frequently]))
      (add norm 0 (by grind only [iff_self_iff]))
      (add norm 0 (by grind only [forall_and]))
      (add norm 0 (by grind only [Classical.not_not]))
      (add norm 0 (by grind only [iff_def]))
      (add norm 0 (by grind only [Filter.frequently_iff]))
      (add norm 0 (by grind only [mapClusterPt_iff]))
      (add norm 0 (by grind only [Filter.le_principal_iff]))
      (add norm 0 (by grind only [Prod.forall]))
      (add norm 0 (by grind only [and_imp]))
      (add norm 0 (by grind only [SetCoe.forall']))
      (add norm 0 (by grind only [Filter.HasBasis.le_iff]))
      (add norm 0 (by grind only [forall₂_swap]))

  -- Step 11: Combine all steps to get IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ)
  have h11 : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
    calc
      IsOpen U ↔ U = interior U := by rw [h1]
      _ ↔ ∀ x ∈ U, x ∈ interior U := by rw [h2]
      _ ↔ ∀ x ∈ U, x ∉ closure (Uᶜ) := by rw [h4]
      _ ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by rw [h10]

  exact h11
