
import Mathlib
open Topology Filter

set_option maxHeartbeats 0

theorem putnam_2001_a1
(S : Type*)
[Mul S]
(hS : ∀ a b : S, (a * b) * a = b)
: ∀ a b : S, a * (b * a) = b := by
  intro a b
  have h1 : (b * a) * b = a := by
    exact hS b a

  have h2 : a * (b * a) = ((b * a) * b) * (b * a) := by
    rw [h1]

  have h3 : ((b * a) * b) * (b * a) = b := by
    have h4 : ∀ x y : S, (x * y) * x = y := hS
    exact h4 (b * a) b

  have h5 : a * (b * a) = b := by
    rw [h2, h3]

  exact h5