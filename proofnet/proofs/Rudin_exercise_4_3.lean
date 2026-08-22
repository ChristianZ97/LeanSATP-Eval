
import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z := by
  -- Step 1
  have h1 : z = f ⁻¹' ({(0:ℝ)} : Set ℝ) := by
    clear * - g
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
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
      (add safe 1 (by ring_nf at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add norm 0 (by grind only [Set.mem_singleton_iff]))
      (add norm 0 (by grind only [Set.preimage_singleton_true]))
      (add norm 0 (by grind only [IndexedPartition.proj_fiber]))
      (add norm 0 (by grind only [MeasureTheory.SimpleFunc.map_preimage_singleton]))
      (add norm 0 (by grind only [Set.pairwiseDisjoint_fiber]))
      (add norm 0 (by grind only [Set.preimage_singleton_false]))
      (add norm 0 (by grind only [Set.biUnion_preimage_singleton]))
      (add norm 0 (by grind only [Set.biUnion_singleton]))
      (add norm 0 (by grind only [Set.mem_preimage]))
      (add norm 0 (by grind only [Set.eq_of_mem_singleton]))
      (add norm 0 (by grind only [MeasureTheory.SimpleFunc.measurableSet_fiber]))
      (add norm 0 (by grind only [connectedComponents_preimage_singleton]))
      (add norm 0 (by grind only [Set.preimage_id']))
      (add norm 0 (by grind only [Set.preimage_one]))
      (add norm 0 (by grind only [MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable]))
      (add norm 0 (by grind only [MeasureTheory.Measure.condKernel_apply_of_ne_zero_of_measurableSet]))
      (add norm 0 (by grind only [LocallyConstant.ofIsClopen_fiber_zero]))
      (add norm 0 (by grind only [Set.preimage]))
      (add norm 0 (by grind only [Finset.set_biUnion_preimage_singleton]))
      (add norm 0 (by grind only [Set.preimage_setOf_eq]))
      (add norm 0 (by grind only [Set.preimage_const]))
      (add norm 0 (by grind only [MeasureTheory.measure_mul_right_null]))
      (add norm 0 (by grind only [Set.preimage_const_of_mem]))
      (add norm 0 (by grind only [Set.preimage_singleton_nonempty]))
      (add norm 0 (by grind only [mem_omegaLimit_singleton_iff_map_cluster_point]))
      (add norm 0 (by grind only [MeasureTheory.Measure.addHaar_preimage_continuousLinearMap]))
      (add norm 0 (by grind only [MeasureTheory.Measure.addHaar_preimage_linearMap]))
      (add norm 0 (by grind only [MeasureTheory.measure_preimage_eq_zero_iff_of_countable]))
      (add norm 0 (by grind only [Set.preimage_singleton_eq_empty]))
      (add norm 0 (by grind only [LocallyConstant.ofIsClopen_fiber_one]))
      (add norm 0 (by grind only [LocallyConstant.locallyConstant_eq_of_fiber_zero_eq]))
      (add norm 0 (by grind only [Set.range_sigmaMk]))

  -- Step 2
  have h2 : IsClosed (({(0:ℝ)} : Set ℝ)) := by
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
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [IsClosed]))
      (add norm 0 (by grind only [isClosed_discrete]))
      (add norm 0 (by grind only [IsExposed.isClosed]))
      (add norm 0 (by grind only [isClosed_of_closure_subset]))
      (add norm 0 (by grind only [IsClosed.preimage]))
      (add norm 0 (by grind only [EMetric.isClosed_subsets_of_isClosed]))
      (add norm 0 (by grind only [isClosed_biInter]))
      (add norm 0 (by grind only [IsClosed.inter]))
      (add norm 0 (by grind only [isClosed_iInter]))
      (add norm 0 (by grind only [ultrafilter_isClosed_basic]))
      (add norm 0 (by grind only [Urysohns.CU]))
      (add norm 0 (by grind only [PrimeSpectrum.comap_singleton_isClosed_of_isIntegral]))
      (add norm 0 (by grind only [isClosed_singleton]))
      (add norm 0 (by grind only [WeakDual.CharacterSpace.union_zero_isClosed]))
      (add norm 0 (by grind only [IsClosed.mono]))
      (add norm 0 (by grind only [WeakDual.CharacterSpace.isClosed]))
      (add norm 0 (by grind only [isOpen_compl_iff]))
      (add norm 0 (by grind only [Topology.IsLawson.singleton_isClosed]))
      (add norm 0 (by grind only [Topology.lawsonClosed_of_scottClosed]))
      (add norm 0 (by grind only [isClosed_le]))
      (add norm 0 (by grind only [Topology.IsScott.isClosed_Iic]))
      (add norm 0 (by grind only [isClosed_induced_iff]))
      (add norm 0 (by grind only [DiscreteQuotient.isClosed_preimage]))
      (add norm 0 (by grind only [OrderClosedTopology]))
      (add norm 0 (by grind only [OpenSubgroup.isClosed]))
      (add norm 0 (by grind only [IsClopen.preimage]))
      (add norm 0 (by grind only [IsSeqClosed.isClosed]))
      (add norm 0 (by grind only [Topology.lawsonClosed_of_lowerClosed]))
      (add norm 0 (by grind only [isClosed_le_of_isClosed_nonneg]))
      (add norm 0 (by grind only [IsClosed.trans]))
      (add norm 0 (by grind only [CategoryTheory.GrothendieckTopology.IsClosed]))
      (add norm 0 (by grind only [isClosed_Ici]))

  -- Step 3
  have h3 : IsClosed (f ⁻¹' ({(0:ℝ)} : Set ℝ)) := by
    clear * - h h2
    exact IsClosed.preimage h h2

  -- Step 4
  have h4 : IsClosed z := by
    clear * - h1 h3
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
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [IsClosed.preimage]))
      (add norm 0 (by grind only [IsClosed]))
      (add norm 0 (by grind only [isClosed_singleton]))
      (add norm 0 (by grind only [IsClopen.preimage]))
      (add norm 0 (by grind only [IsExposed.isClosed]))
      (add norm 0 (by grind only [isClosed_discrete]))
      (add norm 0 (by grind only [isClosed_of_closure_subset]))
      (add norm 0 (by grind only [IsClosed.inter]))
      (add norm 0 (by grind only [Topology.lawsonClosed_of_scottClosed]))
      (add norm 0 (by grind only [DiscreteQuotient.isClosed_preimage]))
      (add norm 0 (by grind only [isClosed_iInter]))
      (add norm 0 (by grind only [isClosed_biInter]))
      (add norm 0 (by grind only [ultrafilter_isClosed_basic]))
      (add norm 0 (by grind only [EMetric.isClosed_subsets_of_isClosed]))
      (add norm 0 (by grind only [isClosed_le]))
      (add norm 0 (by grind only [WeakDual.CharacterSpace.union_zero_isClosed]))
      (add norm 0 (by grind only [Topology.lawsonClosed_of_lowerClosed]))
      (add norm 0 (by grind only [IsClosed.mono]))
      (add norm 0 (by grind only [isClosed_induced_iff]))
      (add norm 0 (by grind only [PrimeSpectrum.comap_singleton_isClosed_of_isIntegral]))
      (add norm 0 (by grind only [Urysohns.CU]))
      (add norm 0 (by grind only [Homeomorph.isClosed_preimage]))
      (add norm 0 (by grind only [isClosed_eq]))
      (add norm 0 (by grind only [LocallyConstant.ofIsClopen_fiber_one]))
      (add norm 0 (by grind only [isClosed_le_of_isClosed_nonneg]))
      (add norm 0 (by grind only [GromovHausdorff.Cb]))
      (add norm 0 (by grind only [Topology.IsLawson.singleton_isClosed]))
      (add norm 0 (by grind only [WeakDual.CharacterSpace.isClosed]))
      (add norm 0 (by grind only [isClosed_le_prod]))
      (add norm 0 (by grind only [LocallyConstant.ofIsClopen_fiber_zero]))
      (add norm 0 (by grind only [OnePoint.isClosed_iff_of_mem]))
      (add norm 0 (by grind only [Profinite.NobelingProof.isClosed_proj]))

  exact h4
