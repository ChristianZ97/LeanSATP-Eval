import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12a_2021_p14 :
  ((∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) *
    ∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k)) = 21000 := by
  have h_sum1_val : ∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2) = 210 * Real.logb 5 3 := by
    have h₀ : (0 : ℝ) < 5 := by norm_num;
    simp [logb, div_eq_mul_inv, mul_add]
    norm_num <;> simp [Finset.sum_Icc_succ_top] <;> ring_nf

  have h_term2_simp : ∀ k ∈ Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k) = Real.logb 3 5 := by
    intro k hk
    clear * - hk
    simp [logb, Finset.mem_Icc.mp hk]
    have h25 : (25 : ℝ) = 5 ^ 2 := by norm_cast
    simp_all [show (9 : ℝ) = 3 ^ 2 by norm_cast]
    rcases hk with ⟨_, hk⟩ <;> field_simp <;> ring

  simp [h_sum1_val, Finset.sum_congr rfl h_term2_simp, h_sum1_val] <;> ring
  norm_num [logb, if_false]
