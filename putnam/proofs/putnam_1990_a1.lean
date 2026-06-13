
import Mathlib
open Filter Topology Nat

set_option maxHeartbeats 0

abbrev putnam_1990_a1_solution : (ℕ → ℤ) × (ℕ → ℤ) :=
  ⟨fun n => ↑(n.factorial), fun n => ↑(2 ^ n)⟩
theorem putnam_1990_a1
  (T : ℕ → ℤ)
  (hT012 : T 0 = 2 ∧ T 1 = 3 ∧ T 2 = 6)
  (hTn : ∀ n, T (n + 3) = (n + 7) * T (n + 2) - 4 * (n + 3) * T (n + 1) + (4 * n + 4) * T n) :
  T = putnam_1990_a1_solution.1 + putnam_1990_a1_solution.2 := by
  apply funext
  intro n
  have h_main : ∀ k, T k = ↑(k.factorial) + ↑(2 ^ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases' k with k_value
      · simp_all only [not_lt_zero', IsEmpty.forall_iff, implies_true, factorial_zero, cast_one, pow_zero, Int.reduceAdd]
      · simp_all only [lt_add_iff_pos_left, add_pos_iff, lt_one_iff, pos_of_gt, or_true, factorial_zero, cast_one, pow_zero,
          Int.reduceAdd, true_and]
        rcases k_value with (_ | _ | k_value) <;> simp_all [factorial]
        specialize ih k_value (by omega)
        simp_all only
        ring_nf <;> simp [pow_succ] <;> ring_nf

  exact h_main n
