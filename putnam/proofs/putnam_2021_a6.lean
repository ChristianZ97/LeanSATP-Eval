
import Mathlib

open Filter Topology

set_option maxHeartbeats 0

abbrev putnam_2021_a6_solution : Prop := ∀ (P : Polynomial ℤ), 
    (∀ n : ℕ, P.coeff n = 0 ∨ P.coeff n = 1) →
    (∃ Q R : Polynomial ℤ, Q.degree > 0 ∧ R.degree > 0 ∧ P = Q * R) →
    (P.eval 2 ≠ 0 ∧ P.eval 2 ≠ 1 ∧ ¬Prime (P.eval 2))
theorem putnam_2021_a6 :
  (∀ P, (∀ n : ℕ, P.coeff n = 0 ∨ P.coeff n = 1) →
    (∃ Q R : Polynomial ℤ, Q.degree > 0 ∧ R.degree > 0 ∧ P = Q * R) →
    (P.eval 2 ≠ 0 ∧ P.eval 2 ≠ 1 ∧ ¬Prime (P.eval 2)))

  ↔ putnam_2021_a6_solution := by
  rw [iff_iff_eq]