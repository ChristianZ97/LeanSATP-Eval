
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have deg : (X ^ 4 - 4 * X ^ 3 + 6 : ℤ[X]).degree = 4
  · compute_degree!
  · apply irreducible_of_eisenstein_criterion (P := Ideal.span { 2 })
    · rw [Ideal.span_singleton_prime (by norm_num), Int.prime_iff_natAbs_prime]
      norm_cast

    · have : (X ^ 4 - 4 * X ^ 3 + 6 : ℤ[X]).leadingCoeff = 1
      · monicity!
      · rw [Ideal.mem_span_singleton, this]
        norm_num

    · intro n hn
      rw [deg] at hn
      norm_cast at hn
      rw [mem_span_singleton]
      interval_cases n <;> simp

    · rw [deg]
      norm_cast

    · norm_num
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      decide

    · refine Monic.isPrimitive (by monicity!)