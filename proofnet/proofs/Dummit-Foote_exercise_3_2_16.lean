
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  simp