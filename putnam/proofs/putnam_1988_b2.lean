
import Mathlib
open Set Filter Topology

set_option maxHeartbeats 0

abbrev putnam_1988_b2_solution : Prop := True
theorem putnam_1988_b2
: (∀ x y : ℝ, (y ≥ 0 ∧ y * (y + 1) ≤ (x + 1) ^ 2) → (y * (y - 1) ≤ x ^ 2)) ↔ putnam_1988_b2_solution := by
  apply Iff.intro
  . intro h; trivial
  . intro _ x y h_cond
    rcases h_cond with ⟨h_y_nonneg, h_hyp⟩

    have h1 : y^2 + y ≤ (x+1)^2 := by
      clear * - h_hyp
      (nlinarith)

    have h2 : 4*y^2 + 4*y ≤ 4*(x+1)^2 := by
      clear * - h1
      (nlinarith)

    have h3 : (2*y+1)^2 - 1 ≤ 4*(x+1)^2 := by
      clear * - h2
      simp_all only [tsub_le_iff_right]
      (nlinarith)

    have h4 : (2*y+1)^2 ≤ 4*x^2 + 8*x + 5 := by
      clear * - h3
      simp_all only [tsub_le_iff_right]
      (nlinarith)

    have h5_pos : 0 ≤ 2*y+1 := by
      clear * - h_y_nonneg
      simp_all only [ge_iff_le]
      (nlinarith)

    have h5_root : 2*y+1 ≤ Real.sqrt (4*x^2 + 8*x + 5) := by
      clear * - h5_pos h4
      apply Real.le_sqrt_of_sq_le <;> nlinarith [sq_nonneg (2 * x + 2 - (2 * y + 1))]

    have h6 : 2*y ≤ Real.sqrt (4*x^2 + 8*x + 5) - 1 := by
      clear * - h5_root
      (nlinarith)

    have h7 : y ≤ (Real.sqrt (4*x^2 + 8*x + 5) - 1) / (2:ℝ) := by
      clear * - h6
      (nlinarith)

    let bound2 : ℝ := (Real.sqrt (4*x^2 + 1) + 1) / (2:ℝ)

    have h_target_equiv : y * (y - 1) ≤ x ^ 2 ↔ y ≤ bound2 := by
      clear * - h_y_nonneg
      simp_all only [ge_iff_le, bound2]
      rw [← sub_nonneg] at h_y_nonneg
      simp_all only [sub_zero]
      constructor <;> intro h_bound
      · nlinarith [Real.sqrt_nonneg (4 * x ^ 2 + 1), Real.mul_self_sqrt (by nlinarith : 0 ≤ 4 * x ^ 2 + 1)]
      · rcases le_total y 1 with hy | hy <;> nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * x ^ 2 + 1)]

    have h15 : (Real.sqrt (4*x^2 + 8*x + 5) - 1) / (2:ℝ) ≤ bound2 := by
      have h16 : Real.sqrt (4*x^2 + 8*x + 5) ≤ Real.sqrt (4*x^2 + 1) + 2 := by
        have h17 : 4*x^2 + 8*x + 5 ≤ 4*x^2 + 1 + 4 + 4*Real.sqrt (4*x^2 + 1) := by
          have h18 : 8*x ≤ 4*Real.sqrt (4*x^2 + 1) := by
            have h19 : 2*x ≤ Real.sqrt (4*x^2 + 1) := by
              have h20 : 4*x^2 ≤ 4*x^2 + 1 := by
                have h21 : 0 ≤ 1 := by norm_num
                clear * - h21
                simp_all only [zero_le, le_add_iff_nonneg_right, zero_le_one]

              clear * - h20
              simp_all only [le_add_iff_nonneg_right, zero_le_one, ge_iff_le]
              have h_nonneg := sq_nonneg x
              simp_all only [ge_iff_le]
              apply Real.le_sqrt_of_sq_le <;> nlinarith [sq_nonneg (2 * x - 1), sq_nonneg (2 * x + 1)]

            clear * - h19
            simp_all only [ge_iff_le]
            (nlinarith)

          clear * - h18
          simp_all only [ge_iff_le]
          (nlinarith)

        clear * - h17
        simp_all only [ge_iff_le]
        repeat' rw [Real.sqrt_le_left]
        · nlinarith [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 * x ^ 2 + 1)]
        · exact le_add_of_le_of_nonneg (by nlinarith [Real.sqrt_nonneg (4 * x ^ 2 + 1)]) (by positivity)

      have h15_derived : (Real.sqrt (4*x^2 + 8*x + 5) - 1) / (2:ℝ) ≤ (Real.sqrt (4*x^2 + 1) + 1) / (2:ℝ) := by
        clear * - h16
        (nlinarith)

      exact h15_derived

    have h22 : y * (y - 1) ≤ x ^ 2 := by
      have h_y_le_bound2 : y ≤ bound2 := by
        calc
        y ≤ (Real.sqrt (4*x^2 + 8*x + 5) - 1) / (2:ℝ) := h7
        _ ≤ bound2 := h15

      rw [h_target_equiv]
      exact h_y_le_bound2

    exact h22