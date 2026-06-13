import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    (∑ k in S, k) = -6 := by
  let r1 : ℝ := 8
  have h1_eq : (r1 + 3) ^ 2 = (121 : ℝ) := by
    clear * -
    simp_all only [r1]
    (ring)

  have h1_in_S : r1 ∈ S := by
    clear * - h₀ h1_eq
    simp_all only [r1]

  let r2 : ℝ := -14
  have h2_eq : (r2 + 3) ^ 2 = (121 : ℝ) := by
    clear * -
    simp_all only [r2]
    (ring)

  have h2_in_S : r2 ∈ S := by
    clear * - h₀ h2_eq
    simp_all only [r2]

  have h_unique_roots : ∀ (x : ℝ), (x + 3) ^ 2 = (121 : ℝ) → (x = r1 ∨ x = r2) := by
    clear * -
    simp_all only [r1, r2]
    intro x hor
    have ht : x + 3 = 11 ∨ x + 3 = -11
    · exact mul_self_eq_mul_self_iff.mp (by linarith)
    · rcases ht with ht | ht <;> [left; right] <;> linarith

  have h_S_def : S = ({r1, r2} : Finset ℝ) := by
    clear * - h₀ h1_in_S h2_in_S h_unique_roots
    simp_all only [r2, r1]
    ext a : 1
    simp_all only [Finset.mem_insert, Finset.mem_singleton, r2, r1]
    apply Iff.intro
    · intro a_1
      simp_all only [r2, r1]
    · intro a_1
      cases a_1 with
      | inl h =>
        subst h
        simp_all only [r2, r1]
      | inr h_1 =>
        subst h_1
        simp_all only [r2, r1]

  have h_sum_interm : (∑ k in S, k) = r1 + r2 := by
    clear * - h_S_def
    subst h_S_def
    simp_all only [r1, r2]
    (norm_num [*] at *)

  have h_sum_final : r1 + r2 = (-6 : ℝ) := by
    clear * -
    aesop
    (add safe 1 (by field_simp))
    (add safe 2 (by ring))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Quaternion.self_add_star | rw [Quaternion.self_add_star] | simp only [Quaternion.self_add_star]))
    (add unsafe 40% (by first | apply Quaternion.star_add_self | rw [Quaternion.star_add_self] | simp only [Quaternion.star_add_self]))
    (add unsafe 40% (by first | apply Quaternion.star_add_self' | rw [Quaternion.star_add_self'] | simp only [Quaternion.star_add_self']))
    (add unsafe 40% (by first | apply mul_two | rw [mul_two] | simp only [mul_two]))

  have h_result : (∑ k in S, k) = (-6 : ℝ) := by
    clear * - h_sum_interm h_sum_final
    simp_all only [r1, r2]

  exact h_result
