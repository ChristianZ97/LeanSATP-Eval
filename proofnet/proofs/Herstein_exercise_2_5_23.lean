
import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_2_5_23 {G : Type*} [Group G]
  (hG : ∀ (H : Subgroup G), H.Normal) (a b : G) :
  ∃ (j : ℤ) , b*a = a^j * b:= by
  let H := Subgroup.zpowers a
  have Hnormal := hG H
  have : b * a * b⁻¹ ∈ H
  · exact Hnormal.conj_mem a (Subgroup.mem_zpowers a) b
  · rw [Subgroup.mem_zpowers_iff] at this
    rcases this with ⟨k, hk⟩
    use k
    rw [hk]
    group