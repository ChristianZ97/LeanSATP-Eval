import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem induction_prod1p1onk3le3m1onn (n : ℕ) (h₀ : 0 < n) :
  (∏ k in Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3)) ≤ (3 : ℝ) - 1 / ↑n := by
  let P : ℕ → ℝ := fun n ↦ ∏ k in Finset.Icc 1 n, (1 + (1 : ℝ) / (k : ℝ) ^ 3)
  let B : ℕ → ℝ := fun n ↦ (3 : ℝ) - 1 / (n : ℝ)
  have h_induction : ∀ (m : ℕ), 0 < m → P m ≤ B m := by
    intro m hm
    induction' hm with m hm IH
    · -- Base case: m = 1
      have h_p1 : P 1 = 2 := by
        simp only [one_div, Finset.Icc_self, Finset.prod_singleton, Nat.cast_one, one_pow, inv_one, P] at *
        (nlinarith)

      have h_b1 : B 1 = 2 := by
        simp_all only [one_div, Finset.Icc_self, Finset.prod_singleton, Nat.cast_one, one_pow, inv_one, P, B]
        (linarith)

      have h_base : P 1 ≤ B 1 := by
        clear * - h_p1 h_b1
        simp_all only [one_div, Finset.Icc_self, Finset.prod_singleton, Nat.cast_one, one_pow, inv_one, le_refl, P, B]

      exact h_base

    · -- Inductive step: assume P(m) ≤ B(m), prove P(m+1) ≤ B(m+1)
      have h_ih : P m ≤ B m := IH
      have h_rec_def : P (m + 1) = P m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) := by
        have h1 : P (m + 1) = ∏ k in Finset.Icc 1 (m + 1), (1 + (1 : ℝ) / (k : ℝ) ^ 3) := rfl
        have h2 : P m = ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / (k : ℝ) ^ 3) := rfl
        have h3 : Finset.Icc 1 (m + 1) = Finset.Icc 1 m ∪ {m + 1} := by
          clear * -
          ext n
          cases n
          · simp [Nat.succ_le]
          · · simp; omega

        have h4 : (∏ k in Finset.Icc 1 (m + 1), (1 + (1 : ℝ) / (k : ℝ) ^ 3)) = (∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / (k : ℝ) ^ 3)) * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) := by
          clear * - h3
          rw [h3, Finset.prod_union]
          · simp
          · simp

        clear * - h1 h2 h4
        simp_all only [one_div, P]

      have h_step1 : P (m + 1) ≤ B m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) := by
        have h1 : P (m + 1) = P m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) := h_rec_def
        have h2 : P m ≤ B m := h_ih
        have h3 : (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) ≥ 0 := by
          have h_pos : ((m + 1) : ℝ) > 0 := by
            clear * - hm
            simp_all only [succ_eq_add_one, zero_add, le_eq, gt_iff_lt]
            (linarith)

          have h_pow_pos : ((m + 1) : ℝ) ^ 3 > 0 := by
            clear * - h_pos
            simp_all only [gt_iff_lt, pow_succ_pos]

          clear * - h_pos h_pow_pos
          simp only [gt_iff_lt, one_div, ge_iff_le] at *
          (bound )

        clear * - h1 h2 h3
        simp_all only [one_div, ge_iff_le, P, B]
        (nlinarith)

      have h_expand : B m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) = 3 + 3 / ((m + 1) : ℝ) ^ 3 - 1 / (m : ℝ) - 1 / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) := by
        have h1 : B m = (3 : ℝ) - 1 / (m : ℝ) := rfl
        have h2 : (3 : ℝ) - 1 / (m : ℝ) = (3 : ℝ) + 0 - 1 / (m : ℝ) := by
          clear * -
          simp_all only [one_div, add_zero]

        clear * - h1 h2
        simp_all only [one_div, add_zero, mul_inv_rev, B]
        (grind only [div_div])

      have h_key_ineq : 3 + 3 / ((m + 1) : ℝ) ^ 3 - 1 / (m : ℝ) - 1 / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) ≤ 3 - 1 / ((m + 1) : ℝ) := by
        have h1 : 3 / ((m + 1) : ℝ) ^ 3 - 1 / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) ≤ 1 / (m : ℝ) - 1 / ((m + 1) : ℝ) := by
          have h2 : 3 / ((m + 1) : ℝ) ^ 3 - 1 / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) = (3 * (m : ℝ) - 1) / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) := by
            clear * - hm
            simp_all only [succ_eq_add_one, zero_add, le_eq, one_div, mul_inv_rev]
            (ring)
            (field_simp)

          have h3 : 1 / (m : ℝ) - 1 / ((m + 1) : ℝ) = 1 / ((m : ℝ) * ((m + 1) : ℝ)) := by
            clear * - hm
            simp_all only [succ_eq_add_one, zero_add, le_eq, one_div, mul_inv_rev]
            (field_simp [*] at *)
            simp_all only [add_sub_cancel_left]

          have h4 : (3 * (m : ℝ) - 1) / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) ≤ 1 / ((m : ℝ) * ((m + 1) : ℝ)) := by
            have h5 : 3 * (m : ℝ) - 1 ≤ ((m + 1) : ℝ) ^ 2 := by
              have h6 : 0 ≤ ((m : ℝ) - 1/2 : ℝ) ^ 2 + 7/4 := by
                clear * -
                simp_all only [one_div]
                (nlinarith)

              have h7 : ((m : ℝ) - 1/2 : ℝ) ^ 2 + 7/4 = (m : ℝ) ^ 2 - (m : ℝ) + 2 := by
                clear * -
                simp_all only [one_div]
                (linarith)

              have h8 : (m : ℝ) ^ 2 - (m : ℝ) + 2 ≥ 0 := by
                clear * - h6 h7
                simp_all only [one_div, ge_iff_le]

              have h9 : 3 * (m : ℝ) - 1 ≤ (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1 := by
                clear * - h8
                simp_all only [ge_iff_le, tsub_le_iff_right]
                (nlinarith)

              have h10 : (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1 = ((m + 1) : ℝ) ^ 2 := by
                clear * -
                (linarith)

              clear * - h9 h10
              simp_all only [tsub_le_iff_right]

            clear * - h5 hm
            simp_all only [succ_eq_add_one, zero_add, le_eq, tsub_le_iff_right, one_div, mul_inv_rev, ge_iff_le]
            (ring)
            simp_all only [tsub_le_iff_right]
            (ring)
            (field_simp)
            (nlinarith)

          clear * - h2 h3 h4
          simp_all only [one_div, mul_inv_rev]

        clear * - h1
        simp_all only [one_div, mul_inv_rev, tsub_le_iff_right, ge_iff_le]
        (linarith)

      have h_quadratic : (m : ℝ) ^ 2 - (m : ℝ) + 2 ≥ 0 := by
        have h1 : (m : ℝ) ^ 2 - (m : ℝ) + 2 = ((m : ℝ) - 1/2 : ℝ) ^ 2 + 7/4 := by
          clear * -
          simp_all only [one_div]
          (linarith)

        have h2 : ((m : ℝ) - 1/2 : ℝ) ^ 2 + 7/4 ≥ 0 := by
          clear * -
          simp_all only [one_div, ge_iff_le]
          (nlinarith)

        clear * - h1 h2
        simp_all only [one_div, ge_iff_le]

      have h_final : P (m + 1) ≤ B (m + 1) := by
        have h1 : P (m + 1) ≤ B m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) := h_step1
        have h2 : B m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) ≤ B (m + 1) := by
          simp_all only [succ_eq_add_one, zero_add, le_eq, one_div, mul_inv_rev, tsub_le_iff_right, ge_iff_le, Nat.cast_add, Nat.cast_one, P, B]

        clear * - h1 h2
        simp_all only [one_div, Nat.cast_add, Nat.cast_one, ge_iff_le, P, B]
        (nlinarith)

      exact h_final

  have h_main : P n ≤ B n := h_induction n h₀
  exact h_main
