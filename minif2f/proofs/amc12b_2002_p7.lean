import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12b_2002_p7 (a b c : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : b = a + 1) (h₂ : c = b + 1)
    (h₃ : a * b * c = 8 * (a + b + c)) : a ^ 2 + (b ^ 2 + c ^ 2) = 77 := by
  have h_step2 : c = a + 2 := by
    clear * - h₁ h₂
    simp_all only [Nat.add_right_cancel_iff, Nat.add_left_cancel_iff]

  have h_step4 : a * (a + 1) * (a + 2) = 8 * (a + (a + 1) + (a + 2)) := by
    clear * - h₁ h₂ h₃
    simp_all only

  have h_step5 : a * (a + 1) * (a + 2) = 8 * (3 * a + 3) := by
    clear * - h_step4
    simp_all only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
    (linarith)

  have h_step6 : a * (a + 1) * (a + 2) = 24 * (a + 1) := by
    clear * - h_step5
    simp_all only
    (linarith)

  have h_a_pos : 0 < a := by
    clear * - h₀
    (linarith)

  have h_denom_ne_zero : a + 1 ≠ 0 := by
    clear * - h_a_pos
    simp_all only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true]

  have h_step7 : a * (a + 2) = 24 := by
    clear * - h_step6 h_denom_ne_zero
    simp_all only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true]
    (nlinarith)

  have h_step8 : a ^ 2 + 2 * a = 24 := by
    clear * - h_step7
    (linarith)

  have h_step11 : a = 4 := by
    clear * - h_step8 h_a_pos
    (nlinarith)

  have h_step12 : b = 5 := by
    clear * - h₁ h_step11
    simp_all only [reduceAdd]

  have h_step13 : c = 6 := by
    clear * - h₂ h_step12
    simp_all only [reduceAdd]

  have h_step14 : a ^ 2 + b ^ 2 + c ^ 2 = 4 ^ 2 + 5 ^ 2 + 6 ^ 2 := by
    clear * - h_step11 h_step12 h_step13
    simp_all only [reducePow, reduceAdd]

  have h_step15 : 4 ^ 2 + 5 ^ 2 + 6 ^ 2 = 16 + 25 + 36 := by
    clear * -
    simp_all only [reducePow, reduceAdd]

  have h_step16 : 16 + 25 + 36 = 41 + 36 := by
    clear * -
    simp_all only [reduceAdd]

  have h_step17 : 41 + 36 = 77 := by
    clear * -
    (linarith)

  have h_final : a ^ 2 + (b ^ 2 + c ^ 2) = 77 := by
    clear * - h_step14 h_step15 h_step16 h_step17
    simp_all only [reducePow, reduceAdd]
    (linarith)

  exact h_final
