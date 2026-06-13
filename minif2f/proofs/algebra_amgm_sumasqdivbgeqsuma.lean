import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  have h1 : (a / sqrt b - sqrt b) ^ 2 ≥ 0 := by
    clear * - h₀
    simp_all only [ge_iff_le]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    (field_simp)
    (bound )

  have h2 : a ^ 2 / b - 2 * a + b ≥ 0 := by
    clear * - h1 h₀
    simp_all only [ge_iff_le]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    (field_simp)
    (field_simp [*] at *)
    (ring_nf at *)
    simp_all only

  have h3 : a ^ 2 / b + b ≥ 2 * a := by
    clear * - h2
    simp_all only [ge_iff_le]
    (nlinarith)

  have h4 : (b / sqrt c - sqrt c) ^ 2 ≥ 0 := by
    clear * - h₀
    simp_all only [ge_iff_le]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    (field_simp)
    (bound )

  have h5 : b ^ 2 / c - 2 * b + c ≥ 0 := by
    clear * - h4 h₀
    simp_all only [ge_iff_le]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    (field_simp)
    (field_simp [*] at *)
    (ring_nf at *)
    simp_all only

  have h6 : b ^ 2 / c + c ≥ 2 * b := by
    clear * - h5
    simp_all only [ge_iff_le]
    (nlinarith)

  have h7 : (c / sqrt d - sqrt d) ^ 2 ≥ 0 := by
    clear * - h₀
    simp_all only [ge_iff_le]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    (field_simp)
    (bound )

  have h8 : c ^ 2 / d - 2 * c + d ≥ 0 := by
    clear * - h7 h₀
    simp_all only [ge_iff_le]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    (field_simp)
    (field_simp [*] at *)
    (ring_nf at *)
    simp_all only

  have h9 : c ^ 2 / d + d ≥ 2 * c := by
    clear * - h8
    simp_all only [ge_iff_le]
    (nlinarith)

  have h10 : (d / sqrt a - sqrt a) ^ 2 ≥ 0 := by
    clear * - h₀
    simp_all only [ge_iff_le]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    (field_simp)
    (bound )

  have h11 : d ^ 2 / a - 2 * d + a ≥ 0 := by
    clear * - h10 h₀
    simp_all only [ge_iff_le]
    obtain ⟨left, right⟩ := h₀
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    (field_simp)
    (field_simp [*] at *)
    (ring_nf at *)
    simp_all only

  have h12 : d ^ 2 / a + a ≥ 2 * d := by
    clear * - h11
    simp_all only [ge_iff_le]
    (nlinarith)

  have h13 : (a ^ 2 / b + b) + (b ^ 2 / c + c) + (c ^ 2 / d + d) + (d ^ 2 / a + a) ≥ 2 * a + 2 * b + 2 * c + 2 * d := by
    clear * - h3 h6 h9 h12
    simp_all only [ge_iff_le]
    (nlinarith)

  have h14 : (a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a) + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    clear * - h13
    simp_all only [ge_iff_le]
    (nlinarith)

  have h15 : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    clear * - h14
    simp_all only [ge_iff_le]
    (nlinarith)

  exact h15