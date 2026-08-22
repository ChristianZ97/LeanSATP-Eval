
import Mathlib

open Topology Filter Set Polynomial Function

set_option maxHeartbeats 0

abbrev putnam_1981_a5_solution : Prop := ∀ (P : Polynomial ℝ),
    let Q P := (X^2 + 1)*P*(derivative P) + X*(P^2 + (derivative P)^2)
    let n P := ({x ∈ Ioi 1 | P.eval x = 0}.ncard : ℝ)
    {x : ℝ | (Q P).eval x = 0}.ncard ≥ 2 * n P - 1
theorem putnam_1981_a5
(Q : Polynomial ℝ → Polynomial ℝ)
(hQ : Q = fun P : Polynomial ℝ => (X^2 + 1)*P*(derivative P) + X*(P^2 + (derivative P)^2))
(n : Polynomial ℝ → ℝ)
(hn : n = fun P : Polynomial ℝ => ({x ∈ Ioi 1 | P.eval x = 0}.ncard : ℝ))
: (∀ P : Polynomial ℝ, {x : ℝ | (Q P).eval x = 0}.ncard ≥ 2*(n P) - 1) ↔ putnam_1981_a5_solution := by
  simp only [hQ, hn]