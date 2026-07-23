import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    (∑ k in S, k) = 4 := by
  have h_abs_prop : ∀ x : ℝ, abs ((2:ℝ) - x) = 3 ↔ (2:ℝ) - x = 3 ∨ (2:ℝ) - x = (-3:ℝ) := by
    clear * -
    exact fun y ↦ abs_eq (by norm_num)

  have h_case1_equiv : ∀ x : ℝ, (2:ℝ) - x = 3 ↔ x = (-1:ℝ) := by
    clear * -
    (grind only [div_eq_one])

  have h_case2_equiv : ∀ x : ℝ, (2:ℝ) - x = (-3:ℝ) ↔ x = (5:ℝ) := by
    clear * -
    (grind only [div_eq_one])

  have h_member_iff : ∀ x : ℝ, x ∈ S ↔ x = (-1:ℝ) ∨ x = (5:ℝ) := by
    clear * - h₀ h_abs_prop h_case1_equiv h_case2_equiv
    simp_all only [implies_true]

  have h_neg1_root : abs ((2:ℝ) - (-1:ℝ)) = 3 := by
    clear * -
    (field_simp)
    (norm_num)

  have h_neg1_in_S : (-1:ℝ) ∈ S := by
    clear * - h₀ h_neg1_root
    all_goals simp_all [abs_eq]

  have h_5_root : abs ((2:ℝ) - (5:ℝ)) = 3 := by
    clear * -
    (ring_nf)

  have h_5_in_S : (5:ℝ) ∈ S := by
    clear * - h₀ h_5_root
    (ring_nf)
    (simp_all)

  have h_S_is_finite_set : S = {(-1:ℝ), (5:ℝ)} := by
    clear * - h_member_iff h_neg1_in_S h_5_in_S
    simp_all only [true_or, or_true]
    (ext)
    simp_all only [Finset.mem_insert, Finset.mem_singleton]

  have h_sum_substitution : (∑ k in S, k) = (∑ k in {(-1:ℝ), (5:ℝ)}, k) := by
    clear * - h_S_is_finite_set
    simp_all only

  have h_sum_expansion : (∑ k in {(-1:ℝ), (5:ℝ)}, k) = ((-1:ℝ) + (5:ℝ)) := by
    clear * -
    (bound )

  have h_final_addition : ((-1:ℝ) + (5:ℝ)) = 4 := by
    clear * -
    (linarith)

  have h_final_result : (∑ k in S, k) = 4 := by
    clear * - h_sum_substitution h_sum_expansion h_final_addition
    simp_all only

  exact h_final_result
