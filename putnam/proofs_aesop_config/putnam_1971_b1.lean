
import Mathlib
open Set MvPolynomial

set_option maxHeartbeats 0

theorem putnam_1971_b1
(S : Type*) [Mul S]
(hself : ∀ x : S, x * x = x)
(h2 : ∀ x y z : S, (x * y) * z = (y * z) * x)
: (∀ x y z : S, (x * y) * z = x * (y * z)) ∧ (∀ x y : S, x * y = y * x) := by
  have h_comm : ∀ x y : S, x * y = y * x := by
    intro x y
    have step1 : x * y = (x * y) * (x * y) := by
      clear * - hself
      simp_all only

    have step2 : (x * y) * (x * y) = (y * (x * y)) * x := by
      clear * - h2
      apply h2

    have step3 : (y * (x * y)) * x = ((x * y) * x) * y := by
      clear * - h2
      simp_all only
      rw [h2]
      simp_all only

    have step4 : (x * y) * x = (x * x) * y := by
      clear * - h2
      rw [h2 x x y]

    have step5 : (x * x) * y = x * y := by
      clear * - hself
      simp_all only

    have step6 : ((x * y) * x) * y = (x * y) * y := by
      clear * - step4 step5
      simp_all only

    have step7 : (x * y) * y = (y * y) * x := by
      clear * - h2
      simp_all only

    have step8 : (y * y) * x = y * x := by
      clear * - hself
      simp_all only

    have step9 : x * y = y * x := by
      clear * - step1 step2 step3 step6 step7 step8
      simp_all only

    exact step9

  have h_assoc : ∀ x y z : S, (x * y) * z = x * (y * z) := by
    intro x y z
    have step10 : x * (y * z) = (y * z) * x := by
      clear * - h_comm
      simp_all only

    have step11 : (y * z) * x = (x * y) * z := by
      clear * - h2 h_comm
      simp_all only

    have step12 : (x * y) * z = x * (y * z) := by
      clear * - step10 step11
      simp_all only

    exact step12

  exact ⟨h_assoc, h_comm⟩