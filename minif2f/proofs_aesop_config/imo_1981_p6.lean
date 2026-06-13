import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem imo_1981_p6 (f : ℕ → ℕ → ℕ) (h₀ : ∀ y, f 0 y = y + 1) (h₁ : ∀ x, f (x + 1) 0 = f x 1)
    (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) : ∀ y, f 4 (y + 1) = 2 ^ (f 4 y + 3) - 3 := by
  intro y
  have h_f0 : ∀ y, f 0 y = y + (1 : ℕ) := by
    clear * - h₀
    intro y
    simp_all only

  have h_f1_0_eq : f 1 0 = f 0 1 := by
    clear * - h₁
    simp_all only

  have h_f0_1 : f 0 1 = (1 : ℕ) + (1 : ℕ) := by
    clear * - h_f0
    simp_all only [reduceAdd]

  have h_f1_0_val : f 1 0 = (2 : ℕ) := by
    clear * - h_f1_0_eq h_f0_1
    simp_all only [reduceAdd]

  have h_f1_rec_def : ∀ y, f 1 (y + 1) = f 0 (f 1 y) := by
    clear * - h₂
    intro y
    simp_all only [zero_add]

  have h_f1_rec_simp : ∀ y, f 1 (y + 1) = f 1 y + (1 : ℕ) := by
    clear * - h_f1_rec_def h_f0
    intro y
    simp_all only

  have h_f1_closed : ∀ y, f 1 y = y + (2 : ℕ) := by
    clear * - h_f1_0_val h_f1_rec_simp
    intro y
    induction y
    · simp_all only [zero_add]
    · simp_all only

  have h_f2_0_eq : f 2 0 = f 1 1 := by
    clear * - h₁
    simp_all only

  have h_f1_1 : f 1 1 = (1 : ℕ) + (2 : ℕ) := by
    clear * - h_f1_closed
    simp_all only [reduceAdd]

  have h_f2_0_val : f 2 0 = (3 : ℕ) := by
    clear * - h_f2_0_eq h_f1_1
    simp_all only [reduceAdd]

  have h_f2_rec_def : ∀ y, f 2 (y + 1) = f 1 (f 2 y) := by
    clear * - h₂
    intro y
    simp_all only [reduceAdd]

  have h_f2_rec_simp : ∀ y, f 2 (y + 1) = f 2 y + (2 : ℕ) := by
    clear * - h_f2_rec_def h_f1_closed
    intro y
    simp_all only

  have h_f2_closed : ∀ y, f 2 y = (2 : ℕ) * y + (3 : ℕ) := by
    clear * - h_f2_0_val h_f2_rec_simp
    intro y
    induction y <;> simp [*, Nat.mul_add, h_f2_rec_simp]

  have h_f3_0_eq : f 3 0 = f 2 1 := by
    clear * - h₁
    simp_all only

  have h_f2_1 : f 2 1 = (2 : ℕ) * (1 : ℕ) + (3 : ℕ) := by
    clear * - h_f2_closed
    simp_all only [mul_one, reduceAdd]

  have h_f3_0_val : f 3 0 = (5 : ℕ) := by
    clear * - h_f3_0_eq h_f2_1
    simp_all only [mul_one, reduceAdd]

  have h_f3_rec_def : ∀ y, f 3 (y + 1) = f 2 (f 3 y) := by
    clear * - h₂
    intro y
    simp_all only [reduceAdd]

  have h_f3_rec_simp : ∀ y, f 3 (y + 1) = (2 : ℕ) * f 3 y + (3 : ℕ) := by
    clear * - h_f3_rec_def h_f2_closed
    intro y
    simp_all only

  have h_f3_rec_plus : ∀ y, f 3 (y + 1) + (3 : ℕ) = (2 : ℕ) * (f 3 y + (3 : ℕ)) := by
    clear * - h_f3_rec_simp
    intro y
    simp_all only
    rfl

  have h_f3_base_plus : f 3 0 + (3 : ℕ) = (2 : ℕ) ^ ((0 : ℕ) + (3 : ℕ)) := by
    clear * - h_f3_0_val
    simp_all only [reduceAdd, zero_add, reducePow]

  have h_f3_shift : ∀ y, f 3 y + (3 : ℕ) = (2 : ℕ) ^ (y + (3 : ℕ)) := by
    clear * - h_f3_base_plus h_f3_rec_plus
    simp_all only [zero_add, reducePow, reduceEqDiff]
    intro y_induction
    induction y_induction <;> simp_all [pow_succ, mul_add] <;>
    linarith [h_f3_rec_plus 0, h_f3_rec_plus 1, h_f3_rec_plus 2]

  have h_f3_closed : ∀ y, f 3 y = (2 : ℕ) ^ (y + (3 : ℕ)) - (3 : ℕ) := by
    clear * - h_f3_shift
    exact λ y ↦ by have h := h_f3_shift y; omega

  have h_f4_rec : f 4 (y + 1) = f 3 (f 4 y) := by
    clear * - h₂
    simp_all only [reduceAdd]

  have h_main : f 4 (y + 1) = (2 : ℕ) ^ (f 4 y + (3 : ℕ)) - (3 : ℕ) := by
    clear * - h_f4_rec h_f3_closed
    simp_all only

  exact h_main