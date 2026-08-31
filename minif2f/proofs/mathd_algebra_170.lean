import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
  S.card = 11 := by
  have h_rhs : (5 : ℚ) + (6 : ℚ) / 10 = (56 : ℚ) / 10 := by
    clear * -
    (linarith)

  have h_unpack : ∀ n : ℤ, abs (n - 2) ≤ (56 : ℚ) / 10 ↔ -(56 : ℚ) / 10 ≤ (n - 2 : ℚ) ∧ (n - 2 : ℚ) ≤ (56 : ℚ) / 10 := by
    intro n
    clear * -
    field_simp [abs_le]
    norm_cast <;> norm_num
    cases abs_cases (n - 2) <;> (try simp [*]) <;> omega

  have h_shift : ∀ n : ℤ, -(56 : ℚ) / 10 ≤ (n - 2 : ℚ) ∧ (n - 2 : ℚ) ≤ (56 : ℚ) / 10 ↔ (-36 : ℚ) / 10 ≤ (n : ℚ) ∧ (n : ℚ) ≤ (76 : ℚ) / 10 := by
    intro n
    clear * -
    simp_all only [tsub_le_iff_right]
    (ring_nf)
    simp_all only [le_neg_add_iff_add_le, and_congr_left_iff]
    intro a
    (ring_nf)

  have h_int_range : ∀ n : ℤ, (-36 : ℚ) / 10 ≤ (n : ℚ) ∧ (n : ℚ) ≤ (76 : ℚ) / 10 ↔ -3 ≤ n ∧ n ≤ 7 := by
    intro n
    clear * -
    norm_num (config := { decide := true })
    field_simp <;> norm_cast at * <;> omega

  have h_S_char : ∀ n : ℤ, n ∈ S ↔ -3 ≤ n ∧ n ≤ 7 := by
    intro n
    clear * - h₀ h_rhs h_unpack h_shift h_int_range
    simp_all [-le_abs]
    norm_num [abs_le] <;> omega

  have h_S : S = Finset.Icc (-3 : ℤ) 7
  · ext a <;> simp [h_S_char]
  · all_goals simp [h_S]
