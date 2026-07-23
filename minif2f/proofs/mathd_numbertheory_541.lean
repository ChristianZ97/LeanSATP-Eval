import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_numbertheory_541 (m n : ℕ) (h₀ : 1 < m) (h₁ : 1 < n) (h₂ : m * n = 2005) :
    m + n = 406 := by

  have h_step2 : 2005 = 5 * 401 := by
    clear * -
    simp_all only [reduceMul]

  have h_dvd_m : m ∣ 2005 := by
    clear * - h₂
    (grind only [dvd_mul_right])

  have h_step3 : m = 1 ∨ m = 5 ∨ m = 401 ∨ m = 2005 := by
    clear * - h_dvd_m h_step2
    have : m ≤ 2005 := Nat.le_of_dvd (by norm_num) h_dvd_m
    interval_cases m <;> (norm_num at *)

  have h_dvd_n : n ∣ 2005 := by
    clear * - h₂
    (grind only [dvd_mul_left])

  have h_step5 : n = 1 ∨ n = 5 ∨ n = 401 ∨ n = 2005 := by
    clear * - h_dvd_n h_step2
    have : n ≤ 2005 := Nat.le_of_dvd (by omega) h_dvd_n <;> interval_cases n <;> norm_cast

  have h_step6 : 1 < m := by
    clear * - h₀
    (linarith)

  have h_step7 : 1 < n := by
    clear * - h₁
    (linarith)

  have h_step8 : m ≠ 1 := by
    clear * - h_step6
    simp only [ne_eq] at *
    (linarith)

  have h_step9 : n ≠ 1 := by
    clear * - h_step7
    simp only [ne_eq] at *
    (linarith)

  have h_step10 : m = 5 ∨ m = 401 ∨ m = 2005 := by
    clear * - h_step3 h_step8
    simp_all only [false_or, ne_eq]

  have h_step11 : m = 2005 → n = 1 := by
    clear * - h₂
    intro a
    subst a
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀]

  have h_step12 : m ≠ 2005 := by
    clear * - h_step11 h_step9
    simp_all only [ne_eq, imp_false, not_false_eq_true]

  have h_step13 : m = 5 ∨ m = 401 := by
    clear * - h_step10 h_step12
    simp_all only [or_false, ne_eq]

  have h_step14 : m = 5 → n = 401 := by
    clear * - h₂ h_step2
    intro a
    subst a
    simp_all only [reduceMul]
    (linarith)

  have h_step15 : m = 401 → n = 5 := by
    clear * - h₂ h_step2
    intro a
    subst a
    simp_all only [reduceMul]
    (linarith)

  have h_step16 : (m = 5 ∧ n = 401) ∨ (m = 401 ∧ n = 5) := by
    clear * - h_step13 h_step14 h_step15
    (grind only [Nat.eq_zero_or_pos])

  have h_step17 : m + n = 5 + 401 := by
    clear * - h_step16
    simp_all only [reduceAdd]
    (omega)

  have h_step18 : m + n = 406 := by
    clear * - h_step17
    simp_all only [reduceAdd]

  exact h_step18
