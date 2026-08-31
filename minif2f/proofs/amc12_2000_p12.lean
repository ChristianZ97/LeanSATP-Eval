import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12_2000_p12 (a m c : ℕ) (h₀ : a + m + c = 12) :
    a * m * c + a * m + m * c + a * c ≤ 112 := by
  let ra := (a:ℝ)
  let rm := (m:ℝ)
  let rc := (c:ℝ)

  have h_step1 : (ra + 1) * (rm + 1) * (rc + 1) = ra * rm * rc + ra * rm + rm * rc + ra * rc + ra + rm + rc + 1 := by
    clear * -
    simp_all only [ra, rm, rc]
    (linarith)

  have h_step2 : ra * rm * rc + ra * rm + rm * rc + ra * rc = (ra + 1) * (rm + 1) * (rc + 1) - (ra + rm + rc) - 1 := by
    clear * - h_step1
    simp_all only [ra, rm, rc]
    (linarith)

  have h_sum_is_12 : ra + rm + rc = 12 := by
    clear * - h₀
    norm_cast at h₀ <;> aesop
    exact_mod_cast h₀

  have h_step3 : ra * rm * rc + ra * rm + rm * rc + ra * rc = (ra + 1) * (rm + 1) * (rc + 1) - 12 - 1 := by
    clear * - h_step2 h_sum_is_12
    simp_all only [ra, rm, rc]

  have h_step4 : ra * rm * rc + ra * rm + rm * rc + ra * rc = (ra + 1) * (rm + 1) * (rc + 1) - (13:ℝ) := by
    clear * - h_step3
    simp_all only [ra, rm, rc]
    (linarith)

  have h_step5 : (ra + 1) * (rm + 1) * (rc + 1) ≤ (((ra + 1) + (rm + 1) + (rc + 1)) / (3:ℝ)) ^ 3 := by
    clear * -
    apply le_of_sub_nonneg
    ring_nf at *
    field_simp
    nlinarith [sq_nonneg (ra - rm), sq_nonneg (ra - rc), sq_nonneg (rm - rc), mul_self_nonneg (a - m : ℝ), mul_self_nonneg (a - c : ℝ), mul_self_nonneg (m - c : ℝ)]

  have h_step6_group : ((ra + 1) + (rm + 1) + (rc + 1)) = (ra + rm + rc) + 3 := by
    clear * -
    simp_all only [ra, rm, rc]
    (linarith)

  have h_step6_subst : (((ra + 1) + (rm + 1) + (rc + 1)) / (3:ℝ)) = ((ra + rm + rc) + 3) / (3:ℝ) := by
    clear * - h_step6_group
    simp_all only [ra, rm, rc]

  have h_step5_mod : (ra + 1) * (rm + 1) * (rc + 1) ≤ (((ra + rm + rc) + 3) / (3:ℝ)) ^ 3 := by
    clear * - h_step5 h_step6_subst
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj', ra, rm, rc]

  have h_step7_sum : (ra + rm + rc) + 3 = 15 := by
    clear * - h_sum_is_12
    simp_all only [ra, rm, rc]
    (linarith)

  have h_step7_div : ((ra + rm + rc) + 3) / (3:ℝ) = (15:ℝ) / (3:ℝ) := by
    clear * - h_step7_sum
    simp_all only [ra, rm, rc]

  have h_step5_final : (ra + 1) * (rm + 1) * (rc + 1) ≤ ((15:ℝ) / (3:ℝ)) ^ 3 := by
    clear * - h_step5_mod h_step7_div
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj', ra, rm, rc]

  have h_step8_calc : (15:ℝ) / (3:ℝ) = 5 := by
    clear * -
    (linarith)

  have h_step5_cube : (ra + 1) * (rm + 1) * (rc + 1) ≤ 5 ^ 3 := by
    clear * - h_step5_final h_step8_calc
    simp_all only [ra, rm, rc]

  have h_step9_pow : (5:ℝ) ^ 3 = 125 := by
    clear * -
    (linarith)

  have h_step10 : (ra + 1) * (rm + 1) * (rc + 1) ≤ 125 := by
    clear * - h_step5_cube h_step9_pow
    simp only [ra, rm, rc] at *
    (nlinarith)

  have h_step11 : ra * rm * rc + ra * rm + rm * rc + ra * rc ≤ 125 - (13:ℝ) := by
    clear * - h_step4 h_step10
    simp_all only [tsub_le_iff_right, sub_add_cancel, ra, rm, rc]

  have h_arith : 125 - (13:ℝ) = 112 := by
    clear * -
    (linarith)

  have h_step12_real : ra * rm * rc + ra * rm + rm * rc + ra * rc ≤ 112 := by
    clear * - h_step11 h_arith
    simp_all only [ra, rm, rc]

  have h_final : a * m * c + a * m + m * c + a * c ≤ 112 := by
    clear * - h_step12_real
    norm_cast at *
    norm_cast at h_step12_real <;> aesop
    exact_mod_cast h_step12_real

  exact h_final
