import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem aime_1984_p1 (u : ℕ → ℚ) (h₀ : ∀ n, u (n + 1) = u n + 1)
    (h₁ : (∑ k in Finset.range 98, u k.succ) = 137) :
    (∑ k in Finset.range 49, u (2 * k.succ)) = 93 := by
  have h_general_term : ∀ k : ℕ, u (k + 1) = u 1 + (k : ℚ) := by
    clear * - h₀
    intro O
    induction' O with D IH <;> simp_all <;> linarith

  have h_sum_first_98_expansion : (∑ k in Finset.range 98, u k.succ) = (∑ k in Finset.range 98, (u 1 + (k : ℚ))) := by
    clear * - h_general_term
    congr 1 with v
    simpa [succ_eq_add_one] using h_general_term v

  have h_sum_first_98_split : (∑ k in Finset.range 98, (u 1 + (k : ℚ))) = (98 : ℚ) * u 1 + (∑ k in Finset.range 98, (k : ℚ)) := by
    clear * -
    simp [Finset.sum_add_distrib, Finset.sum_range_id]

  have h_sum_int_calc : (∑ k in Finset.range 98, (k : ℚ)) = (4753 : ℚ) := by
    clear * -
    (bound )

  have h_eq_u1 : (98 : ℚ) * u 1 + 4753 = 137 := by
    clear * - h₁ h_sum_first_98_expansion h_sum_first_98_split h_sum_int_calc
    (linarith)

  have h_u1_coefficient : (98 : ℚ) * u 1 = -4616 := by
    clear * - h_eq_u1
    (linarith)

  have h_u1_simplified : (49 : ℚ) * u 1 = -2308 := by
    clear * - h_u1_coefficient
    (linarith)

  have h_sum_even_terms_expansion : (∑ k in Finset.range 49, u (2 * k.succ)) = (∑ k in Finset.range 49, (u 1 + 2 * (k : ℚ) + 1)) := by
    clear * - h_general_term
    refine' Finset.sum_congr rfl fun k hk => _
    have := h_general_term (2 * k.succ)
    have := h_general_term (2 * k + 1)
    norm_num [mul_add] at * <;> linarith

  have h_sum_even_terms_split : (∑ k in Finset.range 49, (u 1 + 2 * (k : ℚ) + 1)) = (49 : ℚ) * u 1 + (∑ k in Finset.range 49, (2 * (k : ℚ) + 1)) := by
    clear * -
    classical simp [Finset.sum_add_distrib]
    first
    | ring
    | simp

  have h_sum_odds_calc : (∑ k in Finset.range 49, (2 * (k : ℚ) + 1)) = (2401 : ℚ) := by
    clear * -
    (bound )

  have h_target_sum_expr : (∑ k in Finset.range 49, u (2 * k.succ)) = (49 : ℚ) * u 1 + 2401 := by
    clear * - h_sum_even_terms_expansion h_sum_even_terms_split h_sum_odds_calc
    (linarith)

  have h_final_result : (∑ k in Finset.range 49, u (2 * k.succ)) = 93 := by
    clear * - h_target_sum_expr h_u1_simplified
    simp_all only [succ_eq_add_one]
    (linarith)

  exact h_final_result
