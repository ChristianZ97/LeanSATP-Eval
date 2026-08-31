import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have h_s1 : b + c = (2:ℝ) - a := by
    clear * - h₁
    (linarith)

  have h_s2 : b * c = (1:ℝ) - a * (b + c) := by
    clear * - h₂
    (linarith)

  have h_s3 : b * c = ((1:ℝ) - a)^2 := by
    clear * - h_s2 h_s1
    simp_all only
    (linarith)

  have h_s4 : ((2:ℝ) - a)^2 - (4:ℝ) * ((1:ℝ) - a)^2 = a * ((4:ℝ) - (3:ℝ) * a) := by
    clear * -
    (linarith)

  have h_s5 : a * ((4:ℝ) - (3:ℝ) * a) ≥ (0:ℝ) := by
    clear * - h_s4 h_s1 h_s3
    by_contra h_neg
    try nlinarith [sq_nonneg (b - c), h_s1, h_s3]

  have h_s6 : (0:ℝ) ≤ a ∧ a ≤ ((4:ℝ) / (3:ℝ)) := by
    clear * - h_s5
    constructor <;> nlinarith [sq_nonneg (4 - 3 * a), sq_nonneg a]

  have h_s7 : (3:ℝ) * a ≤ (2:ℝ) := by
    clear * - h₀ h₁
    (linarith)

  have h_s8 : a ≤ ((2:ℝ) / (3:ℝ)) := by
    clear * - h_s7
    (linarith)

  have h_s9 : (2:ℝ) * a ≤ ((2:ℝ) - a) - Real.sqrt (a * ((4:ℝ) - (3:ℝ) * a)) := by
    clear * - h₀ h_s4 h_s1 h_s3
    let s := a
    any_goals nlinarith [Real.sqrt_nonneg (a * (4 - 3 * a)), Real.mul_self_sqrt (by nlinarith : 0 ≤ a * (4 - 3 * a))]

  have h_s10 : ((2:ℝ) - (3:ℝ) * a) ≥ Real.sqrt (a * ((4:ℝ) - (3:ℝ) * a)) := by
    clear * - h_s9
    simp_all only [ge_iff_le]
    (linarith)

  have h_s11 : ((2:ℝ) - (3:ℝ) * a)^2 ≥ a * ((4:ℝ) - (3:ℝ) * a) := by
    clear * - h_s10 h_s8
    norm_num at h_s10 ⊢
    by_contra I
    rw [sqrt_le_iff] at h_s10 <;> nlinarith [sq_nonneg (a - 2 / 3)]

  have h_s12 : ((12:ℝ) * a^2) - ((16:ℝ) * a) + (4:ℝ) ≥ (0:ℝ) := by
    clear * - h_s11
    simp only [ge_iff_le] at *
    (nlinarith)

  have h_s13 : ((3:ℝ) * a^2) - ((4:ℝ) * a) + (1:ℝ) ≥ (0:ℝ) := by
    clear * - h_s12
    simp only [ge_iff_le] at *
    (nlinarith)

  have h_s14 : ((3:ℝ) * a - (1:ℝ)) * (a - (1:ℝ)) ≥ (0:ℝ) := by
    clear * - h_s13
    simp only [ge_iff_le] at *
    (nlinarith)

  have h_s15 : a ≤ ((1:ℝ) / (3:ℝ)) := by
    clear * - h_s14 h_s8 h_s6
    nlinarith [sq_nonneg (3 * a - 1), sq_nonneg a, sq_nonneg (a - 1)]

  have h_s16 : (0:ℝ) ≤ a ∧ a ≤ ((1:ℝ) / (3:ℝ)) := by
    clear * - h_s6 h_s15
    simp_all only [one_div, and_self]

  have h_s17 : b = (((2:ℝ) - a) - Real.sqrt (a * ((4:ℝ) - (3:ℝ) * a))) / (2:ℝ) := by
    clear * - h₀ h_s1 h_s3 h_s4
    nlinarith [Real.sqrt_nonneg (a * (4 - 3 * a)), Real.sq_sqrt (by nlinarith : 0 ≤ a * (4 - 3 * a))]

  have h_s18 : c = (((2:ℝ) - a) + Real.sqrt (a * ((4:ℝ) - (3:ℝ) * a))) / (2:ℝ) := by
    clear * - h₀ h_s1 h_s3 h_s4
    cases le_total a 0 <;> nlinarith [Real.sq_sqrt (by nlinarith : 0 ≤ a * (4 - 3 * a)), Real.sqrt_nonneg (a * (4 - 3 * a))]

  have h_s19 : (((2:ℝ) - (1:ℝ) / 3) - Real.sqrt ((1:ℝ) / 3 * ((4:ℝ) - (3:ℝ) * (1:ℝ) / 3))) / (2:ℝ) = (1:ℝ) / 3 := by
    clear * -
    simp_all only [one_div, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self, inv_nonneg, ofNat_nonneg, sqrt_mul, sqrt_inv]
    (bound )

  have h_s20 : (((2:ℝ) - (0:ℝ)) - Real.sqrt ((0:ℝ) * ((4:ℝ) - (3:ℝ) * (0:ℝ)))) / (2:ℝ) = (1:ℝ) := by
    clear * -
    simp_all only [sub_zero, mul_zero, zero_mul, Real.sqrt_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

  have h_s21 : ((1:ℝ) / 3) ≤ b ∧ b ≤ (1:ℝ) := by
    clear * - h_s17 h_s19 h_s20 h_s16
    constructor <;> field_simp at * <;> norm_num at *
    · nlinarith [Real.sqrt_nonneg (a * (4 - 3 * a)), Real.sq_sqrt (by nlinarith : 0 ≤ a * (4 - 3 * a))]
    · nlinarith [Real.sqrt_nonneg (a * (4 - 3 * a)), Real.sq_sqrt (by nlinarith : 0 ≤ a * (4 - 3 * a))]

  have h_s22 : (((2:ℝ) - (1:ℝ) / 3) + Real.sqrt ((1:ℝ) / 3 * ((4:ℝ) - (3:ℝ) * (1:ℝ) / 3))) / (2:ℝ) = (4:ℝ) / 3 := by
    clear * -
    simp_all only [one_div, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self, inv_nonneg, ofNat_nonneg, sqrt_mul, sqrt_inv]
    (ring)
    simp_all only [ne_eq, ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀, one_div, one_mul]
    (linarith)

  have h_s23 : (((2:ℝ) - (0:ℝ)) + Real.sqrt ((0:ℝ) * ((4:ℝ) - (3:ℝ) * (0:ℝ)))) / (2:ℝ) = (1:ℝ) := by
    clear * -
    simp_all only [sub_zero, mul_zero, zero_mul, Real.sqrt_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

  have h_s24 : (1:ℝ) ≤ c ∧ c ≤ ((4:ℝ) / 3) := by
    clear * - h_s18 h_s22 h_s23 h_s16
    norm_num [h_s18, ← sub_nonneg]
    refine ⟨?_, ?_⟩ <;> nlinarith [Real.sqrt_nonneg (a * (4 - 3 * a)), Real.sq_sqrt (by nlinarith : 0 ≤ a * (4 - 3 * a))]

  have h_s25 : (0:ℝ) ≤ a ∧ a ≤ (1:ℝ) / 3 ∧ (1:ℝ) / 3 ≤ b ∧ b ≤ (1:ℝ) ∧ (1:ℝ) ≤ c ∧ c ≤ (4:ℝ) / 3 := by
    clear * - h_s16 h_s21 h_s24
    simp_all only [one_div, and_self]

  exact h_s25
