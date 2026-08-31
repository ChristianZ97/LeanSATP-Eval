import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  have h1 : (a / sqrt b - sqrt b) ^ 2 ≥ 0 := by
    clear * - h₀
    first
    | positivity
    | apply sq_nonneg

  have h2 : a ^ 2 / b - 2 * a + b ≥ 0 := by
    clear * - h1 h₀
    have S := h₀.1
    have b_pos := h₀.2.1
    field_simp [sq, b_pos.ne'] at h1
    field_simp at * <;> nlinarith [Real.sq_sqrt b_pos.le, sq_nonneg (a - b)]

  have h3 : a ^ 2 / b + b ≥ 2 * a := by
    clear * - h2
    simp_all only [ge_iff_le]
    (linarith)

  have h4 : (b / sqrt c - sqrt c) ^ 2 ≥ 0 := by
    clear * - h₀
    apply pow_two_nonneg

  have h5 : b ^ 2 / c - 2 * b + c ≥ 0 := by
    clear * - h4 h₀
    rcases h₀ with ⟨_, _, _, _⟩
    field_simp [sq, mul_add] at h4
    field_simp [sq] at *
    repeat' nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ c)]

  have h6 : b ^ 2 / c + c ≥ 2 * b := by
    clear * - h5
    simp_all only [ge_iff_le]
    (linarith)

  have h7 : (c / sqrt d - sqrt d) ^ 2 ≥ 0 := by
    clear * - h₀
    apply sq_nonneg

  have h8 : c ^ 2 / d - 2 * c + d ≥ 0 := by
    clear * - h7 h₀
    apply le_of_sub_nonneg
    rcases h₀ with ⟨_, _, _, _⟩
    field_simp [sq, mul_add] at *
    nlinarith [Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ d)]

  have h9 : c ^ 2 / d + d ≥ 2 * c := by
    clear * - h8
    simp_all only [ge_iff_le]
    (linarith)

  have h10 : (d / sqrt a - sqrt a) ^ 2 ≥ 0 := by
    clear * - h₀
    first
    | positivity
    | apply sq_nonneg

  have h11 : d ^ 2 / a - 2 * d + a ≥ 0 := by
    clear * - h10 h₀
    obtain ⟨a_pos, b_pos, c_pos, d_pos⟩ := h₀
    field_simp [sq, a_pos.ne'] at h10 ⊢
    nlinarith [Real.mul_self_sqrt a_pos.le, sq_nonneg (d - √a), d_pos]

  have h12 : d ^ 2 / a + a ≥ 2 * d := by
    clear * - h11
    simp_all only [ge_iff_le]
    (linarith)

  have h13 : (a ^ 2 / b + b) + (b ^ 2 / c + c) + (c ^ 2 / d + d) + (d ^ 2 / a + a) ≥ 2 * a + 2 * b + 2 * c + 2 * d := by
    clear * - h3 h6 h9 h12
    simp_all only [ge_iff_le]
    (linarith)

  have h14 : (a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a) + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    clear * - h13
    simp_all only [ge_iff_le]
    (linarith)

  have h15 : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    clear * - h14
    simp_all only [ge_iff_le]
    (linarith)

  exact h15
