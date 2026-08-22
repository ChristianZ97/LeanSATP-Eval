
import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_2_25 {K : Type*} [MetricSpace K] [CompactSpace K] :
  ∃ (B : Set (Set K)), Set.Countable B ∧ IsTopologicalBasis B := by
  let Q := Set.Icc (0 : ℝ) (1 : ℝ)
  have hQ₁ : IsCompact Q := isCompact_Icc
  have h0 : (0 : ℝ) ∈ Q
  · simp only [zero_le_one, Set.mem_Icc, Q]
    simp

  · rcases exists_countable_basis K with ⟨B, B_count, B_basis⟩
    use B
    exact ⟨B_count, B_basis.2⟩