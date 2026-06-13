import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 (f z : ℂ)
    (h₀ : f + 3 * z = 11)
    (h₁ : 3 * (f - 1) - 5 * z = -68) : f = -10 ∧ z = 7 := by
  have h_step3 : 3 * f - 3 - 5 * z = -68 := by
    clear * - h₁
    (ring_nf at *)
    simp_all only

  have h_step4 : 3 * f - 5 * z = -65 := by
    clear * - h_step3
    linear_combination h_step3 + 3

  have h_step5 : f = 11 - 3 * z := by
    clear * - h₀
    linear_combination h₀

  have h_step7 : 33 - 9 * z - 5 * z = -65 := by
    clear * - h_step4 h_step5
    subst h_step5
    (ring_nf at *)
    simp_all only

  have h_step8 : 33 - 14 * z = -65 := by
    clear * - h_step7
    (ring_nf at *)
    simp_all only

  have h_step9 : -14 * z = -98 := by
    clear * - h_step8
    simp_all only [neg_mul, neg_inj]
    linear_combination (norm := (rw [mul_comm]; ring)) h_step8 + 65
    linear_combination (norm := (rw [mul_comm]; ring)) h_step8 * (-4)
    apply eq_of_sub_eq_zero
    simp_all only [sub_zero]
    linear_combination (norm := (simp; ring)) h_step8 * 7
    linear_combination (norm := (rw [mul_comm]; ring)) -h_step8 * 5

  have h_step10 : z = 7 := by
    clear * - h_step9
    simp_all only [neg_mul, neg_inj]
    linear_combination (norm := (simp; ring)) h_step9 / 14

  have h_step11 : f = 11 - 3 * (7 : ℂ) := by
    clear * - h_step5 h_step10
    subst h_step5 h_step10
    simp_all only

  have h_step12 : f = 11 - 21 := by
    clear * - h_step11
    subst h_step11
    simp_all only [sub_right_inj]
    (norm_num [*] at *)

  have h_step13 : f = -10 := by
    clear * - h_step12
    subst h_step12
    (norm_num [*] at *)

  have h_final : f = -10 ∧ z = 7 := by
    clear * - h_step13 h_step10
    subst h_step13 h_step10
    simp_all only [and_self]

  exact h_final