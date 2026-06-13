
import Mathlib
open Polynomial

set_option maxHeartbeats 0

abbrev putnam_1975_a1_solution : ((ℤ × ℤ) → ℤ) × ((ℤ × ℤ) → ℤ) :=
  (fun p => p.1 + p.2 + 1, fun p => p.1 - p.2)
theorem putnam_1975_a1
(nab nxy : (ℤ × ℤ × ℤ) → Prop)
(hnab : nab = fun (n, a, b) => n = (a^2 + (a : ℚ))/2 + (b^2 + (b : ℚ))/2)
(hnxy : nxy = fun (n, x, y) => 4*n + 1 = x^2 + y^2)
: (∀ n a b : ℤ, nab (n, a, b) → nxy (n, putnam_1975_a1_solution.1 (a, b), putnam_1975_a1_solution.2 (a, b))) ∧
∀ n : ℤ, (∃ x y : ℤ, nxy (n, x, y)) → ∃ a b : ℤ, nab (n, a, b) := by
  constructor
  intro n a b h_nab
  have h_step_1 : (n : ℚ) = ((a : ℚ)^2 + (a : ℚ)) / 2 + ((b : ℚ)^2 + (b : ℚ)) / 2 := by
    clear * - hnab h_nab
    subst hnab
    simp_all only

  have h_step_2 : (4 : ℚ) * n = 2 * (a : ℚ)^2 + 2 * (a : ℚ) + 2 * (b : ℚ)^2 + 2 * (b : ℚ) := by
    clear * - h_step_1
    simp_all only
    (field_simp)
    (nlinarith)

  have h_step_3 : (4 : ℚ) * n + 1 = 2 * (a : ℚ)^2 + 2 * (a : ℚ) + 2 * (b : ℚ)^2 + 2 * (b : ℚ) + 1 := by
    clear * - h_step_2
    simp_all only

  let x : ℤ := putnam_1975_a1_solution.1 (a, b)
  let y : ℤ := putnam_1975_a1_solution.2 (a, b)
  have h_step_6 : (x : ℚ)^2 = (a : ℚ)^2 + (b : ℚ)^2 + 1 + 2 * (a : ℚ) * (b : ℚ) + 2 * (a : ℚ) + 2 * (b : ℚ) := by
    dsimp [putnam_1975_a1_solution, x]
    clear * -
    simp_all only [Int.cast_add, Int.cast_one]
    (nlinarith)

  have h_step_7 : (y : ℚ)^2 = (a : ℚ)^2 - 2 * (a : ℚ) * (b : ℚ) + (b : ℚ)^2 := by
    dsimp [putnam_1975_a1_solution, y]
    clear * -
    simp_all only [Int.cast_sub]
    (nlinarith)

  have h_step_8 : (x : ℚ)^2 + (y : ℚ)^2 = 2 * (a : ℚ)^2 + 2 * (b : ℚ)^2 + 2 * (a : ℚ) + 2 * (b : ℚ) + 1 := by
    clear * - h_step_6 h_step_7
    simp_all only [Int.cast_add, Int.cast_one, Int.cast_sub, x, y]
    (nlinarith)

  have h_step_9 : (x : ℚ)^2 + (y : ℚ)^2 = (4 : ℚ) * n + 1 := by
    clear * - h_step_3 h_step_8
    simp_all only [add_left_inj, Int.cast_add, Int.cast_one, Int.cast_sub, y, x]
    (nlinarith)

  have h_step_10 : 4 * n + 1 = x^2 + y^2 := by
    have h_cast : ((x : ℚ)^2 + (y : ℚ)^2) = ((4 * n + 1) : ℚ) := by simpa using h_step_9
    norm_cast at h_cast ⊢
    subst hnxy hnab
    simp_all only [Int.cast_add, Int.cast_one, Int.cast_sub, add_left_inj, y, x]

  simp [putnam_1975_a1_solution, hnxy] at *
  exact h_step_10
  intro n h_nxy_exists
  obtain ⟨x, y, h_xy⟩ := h_nxy_exists
  rw [hnxy] at h_xy
  have h_even_sum_minus_1 : 2 ∣ (x + y - 1) := by
    clear * - h_xy
    simp_all only
    have h₁ := sq_nonneg x
    obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Int.even_or_odd x <;> obtain ⟨l, rfl⟩ | ⟨l, rfl⟩ := Int.even_or_odd y
    · ring_nf at h_xy ⊢ <;> omega
    · try ring_nf at *; omega
    ·
      obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := Int.even_or_odd l <;> obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd k <;>
          ring_nf at h_xy ⊢ <;>
        omega
    ·
      obtain ⟨k', rfl⟩ | ⟨k', rfl⟩ := Int.even_or_odd k <;> obtain ⟨l', rfl⟩ | ⟨l', rfl⟩ := Int.even_or_odd l <;>
          ring_nf at h_xy ⊢ <;>
        omega

  have h_even_diff_minus_1 : 2 ∣ (x - y - 1) := by
    clear * - h_even_sum_minus_1 h_xy
    simp_all only
    (omega)

  let a : ℤ := (x + y - 1) / 2
  let b : ℤ := (x - y - 1) / 2
  have h_step_13 : 2 * a + 1 = x + y := by
    clear * - h_even_sum_minus_1
    simp_all only [a]
    (omega)

  have h_step_14 : 2 * b + 1 = x - y := by
    clear * - h_even_diff_minus_1
    simp_all only [b]
    (omega)

  have h_step_15 : 4 * (a^2 + a) = (2 * a + 1)^2 - 1 := by
    clear * -
    simp_all only [a]
    (nlinarith)

  have h_step_16 : 4 * (a^2 + a) = (x + y)^2 - 1 := by
    clear * - h_step_13 h_step_15
    simp_all only [a]

  have h_step_17 : 4 * (b^2 + b) = (2 * b + 1)^2 - 1 := by
    clear * -
    simp_all only [b]
    (nlinarith)

  have h_step_18 : 4 * (b^2 + b) = (x - y)^2 - 1 := by
    clear * - h_step_14 h_step_17
    simp_all only [b]

  have h_step_19 : 4 * (a^2 + a + b^2 + b) = (x + y)^2 + (x - y)^2 - 2 := by
    clear * - h_step_16 h_step_18
    simp_all only [a, b]
    (nlinarith)

  have h_step_20 : (x + y)^2 + (x - y)^2 = 2 * x^2 + 2 * y^2 := by
    clear * -
    (nlinarith)

  have h_step_21 : 4 * (a^2 + a + b^2 + b) = 2 * x^2 + 2 * y^2 - 2 := by
    clear * - h_step_19 h_step_20
    simp_all only [a, b]

  have h_step_22 : 2 * (a^2 + a + b^2 + b) = x^2 + y^2 - 1 := by
    clear * - h_step_21
    simp_all only [a, b]
    (nlinarith)

  have h_step_23 : 2 * (a^2 + a + b^2 + b) = (4 * n + 1) - 1 := by
    clear * - h_step_22 h_xy
    simp_all only [a, b]

  have h_step_24 : a^2 + a + b^2 + b = 2 * n := by
    clear * - h_step_23
    simp_all only [add_sub_cancel_right, a, b]
    (nlinarith)

  have h_step_25 : n = (a^2 + (a : ℚ)) / 2 + (b^2 + (b : ℚ)) / 2 := by
    clear * - h_step_24
    simp_all only [a, b]
    (field_simp)
    (norm_cast at *)
    (nlinarith)

  have h_nab_holds : nab (n, a, b) := by
    clear * - hnab h_step_25
    subst hnab
    simp_all only [a, b]

  exact ⟨a, b, h_nab_holds⟩
