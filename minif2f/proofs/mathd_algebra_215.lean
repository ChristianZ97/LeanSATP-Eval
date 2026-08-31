import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    (∑ k in S, k) = -6 := by
  let r1 : ℝ := 8
  have h1_eq : (r1 + 3) ^ 2 = (121 : ℝ) := by
    clear * -
    simp_all only [r1]
    (linarith)

  have h1_in_S : r1 ∈ S := by
    clear * - h₀ h1_eq
    simp_all only [r1]

  let r2 : ℝ := -14
  have h2_eq : (r2 + 3) ^ 2 = (121 : ℝ) := by
    clear * -
    simp_all only [r2]
    (linarith)

  have h2_in_S : r2 ∈ S := by
    clear * - h₀ h2_eq
    simp_all only [r2]

  have h_unique_roots : ∀ (x : ℝ), (x + 3) ^ 2 = (121 : ℝ) → (x = r1 ∨ x = r2) := by
    clear * -
    simp_all only [r1, r2]
    (grind only [SimpleGraph.Walk.IsEulerian.card_filter_odd_degree])

  have h_S_def : S = ({r1, r2} : Finset ℝ) := by
    clear * - h₀ h1_in_S h2_in_S h_unique_roots
    ext x <;> aesop  (add simp [h₀])

  have h_sum_interm : (∑ k in S, k) = r1 + r2 := by
    clear * - h_S_def
    simp [Finset.sum, h_S_def, Finset.univ]
    norm_num [r1, r2]

  have h_sum_final : r1 + r2 = (-6 : ℝ) := by
    clear * -
    simp_all only [r1, r2]
    (linarith)

  have h_result : (∑ k in S, k) = (-6 : ℝ) := by
    clear * - h_sum_interm h_sum_final
    (linarith)

  exact h_result
