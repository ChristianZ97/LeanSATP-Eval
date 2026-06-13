import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_430 (a b c : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 1 ≤ b ∧ b ≤ 9)
    (h₂ : 1 ≤ c ∧ c ≤ 9) (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c) (h₆ : a + b = c)
    (h₇ : 10 * a + a - b = 2 * c) (h₈ : c * b = 10 * a + a + a) : a + b + c = 8 := by
  have h_11a : (10:ℕ) * a + a = (11:ℕ) * a := by
    clear * -
    (nlinarith)

  have h_step1 : ((11:ℕ) * a) - b = 2 * c := by
    clear * - h₇ h_11a
    simp_all only

  have h_step2 : ((11:ℕ) * a) - b = 2 * (a + b) := by
    clear * - h_step1 h₆
    subst h₆
    simp_all only

  have h_step3 : ((11:ℕ) * a) - b = 2 * a + 2 * b := by
    clear * - h_step2
    simp_all only
    apply mul_add

  have h_step4 : ((11:ℕ) * a) - 2 * a = 2 * b + b := by
    clear * - h_step3
    (omega)

  have h_step5 : (9:ℕ) * a = 3 * b := by
    clear * - h_step4
    (omega)

  have h_step6 : 3 * a = b := by
    clear * - h_step5
    (nlinarith)

  have h_step7 : c = a + 3 * a := by
    clear * - h_step6 h₆
    subst h_step6 h₆
    simp_all only

  have h_step8 : c = 4 * a := by
    clear * - h_step7
    subst h_step7
    (nlinarith)

  have h_12a : 10 * a + a + a = (12:ℕ) * a := by
    clear * -
    (nlinarith)

  have h_step9 : c * b = (12:ℕ) * a := by
    clear * - h₈ h_12a
    simp_all only

  have h_step10 : (4 * a) * (3 * a) = (12:ℕ) * a := by
    clear * - h_step8 h_step6 h_step9
    subst h_step8 h_step6
    simp_all only

  have h_step11 : (12:ℕ) * a * a = (12:ℕ) * a := by
    clear * - h_step10
    simp_all only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀]
    rcases Nat.eq_zero_or_pos a with h | h <;> aesop
    have : 4 * a * (3 * a) = 12 * a := h_step10
    simp_all only
    exact Or.inl (by nlinarith)

  have h_step12 : a = 1 := by
    clear * - h_step11 h₀
    simp_all only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀]
    obtain ⟨left, right⟩ := h₀
    cases h_step11 with
    | inl h =>
    subst h
    simp_all only [le_refl, one_le_ofNat]
    | inr h_1 =>
    subst h_1
    simp_all only [nonpos_iff_eq_zero, one_ne_zero]

  have h_step13 : b = 3 * 1 := by
    clear * - h_step6 h_step12
    subst h_step6 h_step12
    simp_all only [mul_one]

  have h_step14 : b = 3 := by
    clear * - h_step13
    subst h_step13
    simp_all only [mul_one]

  have h_step15 : c = 4 * 1 := by
    clear * - h_step8 h_step12
    subst h_step8 h_step12
    simp_all only [mul_one]

  have h_step16 : c = 4 := by
    clear * - h_step15
    subst h_step15
    simp_all only [mul_one]

  have h_step17 : a + b + c = 1 + 3 + 4 := by
    clear * - h_step12 h_step14 h_step16
    subst h_step14 h_step16 h_step12
    simp_all only [reduceAdd]

  have h_step18 : a + b + c = 8 := by
    clear * - h_step17
    simp_all only [reduceAdd]

  exact h_step18