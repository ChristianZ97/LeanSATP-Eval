
import Mathlib

open Real
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_3_4 : ¬ ∃ x y : ℤ, 3*x^2 + 2 = y^2 := by
  rintro hex
  obtain ⟨x, y, h⟩ := hex
  let h' := h
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Int.even_or_odd x <;> obtain ⟨l, rfl⟩ | ⟨l, rfl⟩ := Int.even_or_odd y
  ·
    obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := Int.even_or_odd k <;> obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd l <;>
        ring_nf at h' <;>

      (omega)

  ·
    obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := Int.even_or_odd l <;> obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd k <;>
        ring_nf at h' <;>

      omega

  · ring_nf at h'
    obtain ⟨l', rfl⟩ | ⟨l', rfl⟩ := Int.even_or_odd l <;> obtain ⟨k', rfl⟩ | ⟨k', rfl⟩ := Int.even_or_odd k <;>
        ring_nf at h' <;>

      omega

  · ring_nf at h'
    obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := Int.even_or_odd k <;> obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd l <;>
        ring_nf at h' <;>

      omega