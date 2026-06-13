import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_598 (a b c d : ℝ) (h₁ : (4 : ℝ) ^ a = 5) (h₂ : (5 : ℝ) ^ b = 6)
  (h₃ : (6 : ℝ) ^ c = 7) (h₄ : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by
  have h_a_log : Real.log ((4 : ℝ) ^ a) = Real.log 5 := by
    clear * - h₁
    simp_all only

  have h_a_prod : a * Real.log 4 = Real.log 5 := by
    clear * - h_a_log
    simp [Real.log_rpow zero_lt_four] at h_a_log <;> linarith

  have h_a_denom_ne_zero : Real.log 4 ≠ 0 := by
    clear * -
    simp only [ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or] at *
    apply Aesop.BuiltinRules.not_intro
    intro a
    (linarith)

  have h_a_val : a = Real.log 5 / Real.log 4 := by
    clear * - h_a_prod h_a_denom_ne_zero
    simp_all only [ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or]
    (field_simp)
    simp_all only

  have h_b_log : Real.log ((5 : ℝ) ^ b) = Real.log 6 := by
    clear * - h₂
    simp_all only

  have h_b_prod : b * Real.log 5 = Real.log 6 := by
    clear * - h_b_log
    simp [Real.log_rpow, eq_comm, mul_comm] at h_b_log <;> linarith

  have h_b_denom_ne_zero : Real.log 5 ≠ 0 := by
    clear * -
    simp_all only [ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or]
    apply Aesop.BuiltinRules.not_intro
    intro a
    (bound )

  have h_b_val : b = Real.log 6 / Real.log 5 := by
    clear * - h_b_prod h_b_denom_ne_zero
    simp_all only [ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or]
    (field_simp)
    simp_all only

  have h_c_log : Real.log ((6 : ℝ) ^ c) = Real.log 7 := by
    clear * - h₃
    simp_all only

  have h_c_prod : c * Real.log 6 = Real.log 7 := by
    clear * - h_c_log
    simp [Real.log_rpow, mul_comm] at * <;> linarith

  have h_c_denom_ne_zero : Real.log 6 ≠ 0 := by
    clear * -
    simp_all only [ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or]
    apply Aesop.BuiltinRules.not_intro
    intro a
    (bound )

  have h_c_val : c = Real.log 7 / Real.log 6 := by
    clear * - h_c_prod h_c_denom_ne_zero
    simp_all only [ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or]
    (field_simp)
    simp_all only

  have h_d_log : Real.log ((7 : ℝ) ^ d) = Real.log 8 := by
    clear * - h₄
    simp_all only

  have h_d_prod : d * Real.log 7 = Real.log 8 := by
    clear * - h_d_log
    simp [Real.log_rpow, eq_comm] at h_d_log
    simp_all only

  have h_d_denom_ne_zero : Real.log 7 ≠ 0 := by
    clear * -
    simp_all only [ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or]
    apply Aesop.BuiltinRules.not_intro
    intro a
    (bound )

  have h_d_val : d = Real.log 8 / Real.log 7 := by
    clear * - h_d_prod h_d_denom_ne_zero
    simp_all only [ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or]
    (field_simp)
    simp_all only

  have h_prod_exp : a * b * c * d = (Real.log 5 / Real.log 4) * (Real.log 6 / Real.log 5) * (Real.log 7 / Real.log 6) * (Real.log 8 / Real.log 7) := by
    clear * - h_a_val h_b_val h_c_val h_d_val
    subst h_d_val h_c_val h_a_val h_b_val
    simp_all only

  have h_tel_scope : a * b * c * d = Real.log 8 / Real.log 4 := by
    clear * - h_prod_exp
    simp_all only
    (field_simp)
    (nlinarith)

  have h_log_8 : Real.log 8 = (3 : ℝ) * Real.log 2 := by
    clear * -
    have h : (8 : ℝ) = (2 : ℝ) ^ 3
    · norm_num
    · simp_all only [Real.log_pow, Nat.cast_ofNat]

  have h_log_4 : Real.log 4 = (2 : ℝ) * Real.log 2 := by
    clear * -
    rw [← Real.log_rpow] <;> norm_num

  have h_final_val : Real.log 8 / Real.log 4 = (3 : ℝ) / 2 := by
    have h_sub : Real.log 8 / Real.log 4 = ((3 : ℝ) * Real.log 2) / ((2 : ℝ) * Real.log 2) := by
      clear * - h_log_8 h_log_4
      simp_all only

    have h_cancel : ((3 : ℝ) * Real.log 2) / ((2 : ℝ) * Real.log 2) = (3 : ℝ) / 2 := by
      clear * - h_sub
      (field_simp)
      (nlinarith)

    subst h_c_val h_b_val h_d_val h_a_val
    simp_all only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, log_eq_zero, OfNat.ofNat_ne_one, false_or,
      isUnit_iff_ne_zero, or_self, not_false_eq_true, IsUnit.div_mul_cancel, div_mul_div_cancel₀']

  rw [h_tel_scope]
  rw [h_final_val]