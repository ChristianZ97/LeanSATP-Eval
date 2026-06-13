
import Mathlib
open Topology Filter

set_option maxHeartbeats 0

theorem putnam_2000_a2 :
  ∀ n : ℕ,
    ∃ N : ℤ,
      ∃ i : Fin 6 → ℕ,
        N > n ∧
        N = (i 0)^2 + (i 1)^2 ∧
        N + 1 = (i 2)^2 + (i 3)^2 ∧
        N + 2 = (i 4)^2 + (i 5)^2 := by
  intro n
  let t : ℕ := n + 1
  let N : ℤ := 4 * ((t:ℤ)^4) + 4 * ((t:ℤ)^2)
  let i : Fin 6 → ℕ := fun k =>
    match k with
    | ⟨0, _⟩ => 2 * t^2
    | ⟨1, _⟩ => 2 * t
    | ⟨2, _⟩ => 2 * t^2 + 1
    | ⟨3, _⟩ => 0
    | ⟨4, _⟩ => 2 * t^2 + 1
    | ⟨5, _⟩ => 1

  have h_t_def : t = n + 1 := rfl
  have h_N_def : N = 4 * ((t:ℤ)^4) + 4 * ((t:ℤ)^2) := rfl
  have h_i0 : i 0 = 2 * t^2 := rfl
  have h_i1 : i 1 = 2 * t := rfl
  have h_i2 : i 2 = 2 * t^2 + 1 := rfl
  have h_i3 : i 3 = 0 := rfl
  have h_i4 : i 4 = 2 * t^2 + 1 := rfl
  have h_i5 : i 5 = 1 := rfl
  have h_step2 : N = (i 0)^2 + (i 1)^2 := by
    clear * - h_N_def h_i0 h_i1
    simp_all only [Nat.cast_add, Nat.cast_one, Fin.isValue, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, N, t, i]
    (nlinarith)

  have h_step3 : N + 1 = 4 * ((t:ℤ)^4) + 4 * ((t:ℤ)^2) + 1 := by
    clear * - h_N_def
    simp_all only [Nat.cast_add, Nat.cast_one, N, t]

  have h_step4 : N + 1 = (i 2)^2 + (i 3)^2 := by
    clear * - h_step3 h_i2 h_i3
    simp_all only [Fin.isValue, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, i, t, N]
    (nlinarith)

  have h_step5 : N + 2 = 4 * ((t:ℤ)^4) + 4 * ((t:ℤ)^2) + 2 := by
    clear * - h_N_def
    simp_all only [Nat.cast_add, Nat.cast_one, N, t]

  have h_step6 : N + 2 = (i 4)^2 + (i 5)^2 := by
    clear * - h_step5 h_i4 h_i5
    simp_all only [Fin.isValue, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, one_pow, i, t, N]
    (nlinarith)

  have h_step7 : 4 * ((t:ℤ)^4) + 4 * ((t:ℤ)^2) > (n:ℤ) := by
    clear * - h_t_def
    simp_all only [Nat.cast_add, Nat.cast_one, gt_iff_lt, t]
    (nlinarith)

  have h_N_gt_n : N > n := by
    clear * - h_N_def h_step7
    simp_all only [Nat.cast_add, Nat.cast_one, gt_iff_lt, N, t]

  use N, i