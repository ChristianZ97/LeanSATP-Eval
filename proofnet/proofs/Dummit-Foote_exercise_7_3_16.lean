
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_7_3_16 {R S : Type*} [Ring R] [Ring S]
  {φ : R →+* S} (hf : Function.Surjective φ) :
  φ '' (center R) ⊆ center S := by
  -- Let x be an element in the center of R.
  let centerR := center R
  -- We want to show that for any y in the image of centerR under φ, y is in the center of S.
  have h_main : ∀ (x : R), x ∈ center R → φ x ∈ center S := by
    intro x hx
    -- Let s be an arbitrary element in S.
    apply Set.mem_center_iff.mpr
    constructor
    · intro a
      rcases hf a with ⟨y, hy⟩
      rw [← hy]
      exact (hx.1 y).map φ
    · intro b c
      rcases hf b with ⟨b', rfl⟩
      rw [mul_assoc]
    · intro a b
      obtain ⟨x', hx'⟩ := hf a
      rw [← hx']
      rw [← mul_assoc]

  -- Finally, we show that the image of the center of R is contained in the center of S.
  -- The statement φ '' (center R) ⊆ center S means that for any y in the image, y is in center S.
  -- By definition of image, y is in the image if there exists x in center R such that φ x = y.
  -- We proved that for any x in center R, φ x is in center S.
  intro y hy
  -- hy : y ∈ φ '' center R
  rcases hy with ⟨x, hx, rfl⟩
  -- Here y = φ x and x ∈ center R
  have h_x_in_center : x ∈ center R := hx
  -- From h_main, we know that φ x ∈ center S
  apply h_main x h_x_in_center
