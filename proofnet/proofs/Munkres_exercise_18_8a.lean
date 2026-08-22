
import Mathlib

open Filter Set TopologicalSpace
open scoped Topology


set_option maxHeartbeats 0

theorem exercise_18_8a {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  IsClosed {x | f x ≤ g x} := by
  -- Step 1: Define A = {x | f x ≤ g x}
  let A : Set X := {x | f x ≤ g x}

  -- Step 2: Define D = {(u, v) ∈ Y × Y | u ≤ v}
  let D : Set (Y × Y) := {p | p.1 ≤ p.2}

  -- Step 3: Define Φ = (f, g)
  let Φ : X → Y × Y := fun x => (f x, g x)

  -- Step 4: Φ(x) = (f(x), g(x)) is by definition

  -- Step 5: A = Φ⁻¹(D)
  have h5 : A = Φ ⁻¹' D := by
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
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Set.preimage_setOf_eq]))
      (add norm 0 (by grind only [Filter.map]))
      (add norm 0 (by grind only [Prod.map]))
      (add norm 0 (by grind only [Set.setOf_forall]))
      (add norm 0 (by grind only [Prod.forall]))
      (add norm 0 (by grind only [Filter.mem_map]))
      (add norm 0 (by grind only [Set.preimage]))
      (add norm 0 (by grind only [Prod]))
      (add norm 0 (by grind only [Filter.le_prod]))
      (add norm 0 (by grind only [Filter.HasBasis.le_iff]))
      (add norm 0 (by grind only [Set.setOf_and]))
      (add norm 0 (by grind only [Filter.HasBasis.ge_iff]))
      (add norm 0 (by grind only [Set.setOf_mem_eq]))
      (add norm 0 (by grind only [Filter.mem_map']))
      (add norm 0 (by grind only [Filter.mem_comap]))
      (add norm 0 (by grind only [Set.mk_preimage_prod_right]))
      (add norm 0 (by grind only [regionBetween]))
      (add norm 0 (by grind only [Continuous.Prod.mk]))
      (add norm 0 (by grind only [TopologicalSpace.nhds_generateFrom]))
      (add norm 0 (by grind only [nhds_prod_eq]))
      (add norm 0 (by grind only [Filter.HasBasis.le_basis_iff]))
      (add norm 0 (by grind only [ContinuousMap.coev]))
      (add norm 0 (by grind only [UniformFun.basis]))
      (add norm 0 (by grind only [Filter.le_def]))
      (add norm 0 (by grind only [UniformFun.gen]))
      (add norm 0 (by grind only [forall_swap]))
      (add norm 0 (by grind only [Prod.forall']))
      (add norm 0 (by grind only [UniformFun.filter]))
      (add norm 0 (by grind only [Set.mem_prod]))
      (add norm 0 (by grind only [Prod.swap]))
      (add norm 0 (by grind only [isOpenMap_iff_nhds_le]))
      (add norm 0 (by grind only [Set.mem_preimage]))

  -- Step 6: cl_{Y×Y}(D) = D (i.e., D is closed in Y×Y)
  have h6 : IsClosed D := by
    clear * -
    apply isClosed_le_prod

  -- Step 7: Φ is continuous (since f and g are continuous)
  have h7 : Continuous Φ := by
    clear * - hf hg
    fun_prop

  -- Step 8: Since D is closed and Φ is continuous, Φ⁻¹(D) is closed
  have h8 : IsClosed (Φ ⁻¹' D) := by
    clear * - h6 h7
    exact h6.preimage h7

  -- Step 9: Therefore, A is closed
  have h9 : IsClosed A := by
    clear * - h5 h8
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [IsClosed.preimage]))
      (add norm 0 (by grind only [IsClopen.preimage]))
      (add norm 0 (by grind only [IsClosed]))
      (add norm 0 (by grind only [isClosed_discrete]))
      (add norm 0 (by grind only [isClosed_induced_iff]))
      (add norm 0 (by grind only [Homeomorph.isClosed_preimage]))
      (add norm 0 (by grind only [IsExposed.isClosed]))
      (add norm 0 (by grind only [IsClosed.inter]))
      (add norm 0 (by grind only [ultrafilter_isClosed_basic]))
      (add norm 0 (by grind only [isClosed_le]))
      (add norm 0 (by grind only [isClosed_of_closure_subset]))
      (add norm 0 (by grind only [DiscreteQuotient.isClosed_preimage]))
      (add norm 0 (by grind only [isClosed_le_prod]))
      (add norm 0 (by grind only [EMetric.isClosed_subsets_of_isClosed]))
      (add norm 0 (by grind only [isClosed_iInter]))
      (add norm 0 (by grind only [Topology.lawsonClosed_of_scottClosed]))
      (add norm 0 (by grind only [isClosed_biInter]))
      (add norm 0 (by grind only [isClosed_le_of_isClosed_nonneg]))
      (add norm 0 (by grind only [WeakDual.CharacterSpace.union_zero_isClosed]))
      (add norm 0 (by grind only [Topology.lawsonClosed_of_lowerClosed]))
      (add norm 0 (by grind only [isClosed_setOf_specializes]))
      (add norm 0 (by grind only [UniformOnFun.isClosed_setOf_continuous]))
      (add norm 0 (by grind only [isOpen_compl_iff]))
      (add norm 0 (by grind only [OnePoint.isClosed_iff_of_mem]))
      (add norm 0 (by grind only [OrderClosedTopology]))
      (add norm 0 (by grind only [WeakDual.CharacterSpace.isClosed]))
      (add norm 0 (by grind only [isClosed_iff_forall_filter]))
      (add norm 0 (by grind only [IsClosed.mono]))
      (add norm 0 (by grind only [isClosed_eq]))
      (add norm 0 (by grind only [continuous_apply]))
      (add norm 0 (by grind only [Topology.IsScott.isClosed_Iic]))
      (add norm 0 (by grind only [IsSeqClosed.isClosed]))

  exact h9
