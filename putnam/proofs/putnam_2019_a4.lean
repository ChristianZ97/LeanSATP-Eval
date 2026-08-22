
import Mathlib

open MeasureTheory Metric Topology Filter

set_option maxHeartbeats 0

abbrev putnam_2019_a4_solution : Prop := ∀ (f : EuclideanSpace ℝ (Fin 3) → ℝ), Continuous f → (∀ C, ∫ x in sphere C 1, f x ∂μH[2] = 0) → f = 0
theorem putnam_2019_a4
    (P : (EuclideanSpace ℝ (Fin 3) → ℝ) → Prop)
    (P_def : ∀ f, P f ↔ ∀ C, ∫ x in sphere C 1, f x ∂μH[2] = 0) :
    (∀ f, Continuous f → P f → f = 0) ↔ putnam_2019_a4_solution := by
  constructor
  · -- Forward direction: Assume the implication for P, prove it for the explicit definition.
    intro h
    rintro f hc hf_explicit
    have hP : P f := by
      simp_all [P_def]

    have hf_zero : f = 0 := by
      apply h f hc hP

    exact hf_zero

  · -- Backward direction: Assume the explicit statement, prove the one for P.
    intro h
    rintro f hf_cont hP
    have hf_explicit : ∀ C, ∫ x in sphere C 1, f x ∂μH[2] = 0 := by
      rw [P_def] at hP
      exact hP

    have hf_zero : f = 0 := by
      apply h f hf_cont hf_explicit

    exact hf_zero