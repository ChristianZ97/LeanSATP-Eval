
import Mathlib
open Matrix

set_option maxHeartbeats 0

theorem putnam_2012_a2
(S : Type*) [CommSemigroup S]
(a b c : S)
(hS : ∀ x y : S, ∃ z : S, x * z = y)
(habc : a * c = b * c)
: a = b := by
  obtain ⟨x, hx⟩ := hS c a
  obtain ⟨y, hy⟩ := hS c b
  have step1 : c * x = a := hx
  have step2 : c * y = b := hy
  have step3 : a * c = (c * x) * c := by
    clear * - step1
    subst step1
    simp_all only

  have step4 : (c * x) * c = (c * c) * x := by
    clear * -
    rw [mul_right_comm]

  have step5 : a * c = (c * c) * x := by
    clear * - step3 step4
    simp_all only

  have step6 : b * c = (c * y) * c := by
    clear * - step2
    subst step2
    simp_all only

  have step7 : (c * y) * c = (c * c) * y := by
    clear * -
    rw [mul_assoc]
    rw [mul_left_comm]
    rw [mul_comm]

  have step8 : b * c = (c * c) * y := by
    clear * - step6 step7
    simp_all only

  have step9 : (c * c) * x = (c * c) * y := by
    clear * - step5 habc step8
    simp_all only

  obtain ⟨u, hu⟩ := hS (c * c) c
  have step10 : (c * c) * u = c := hu
  have step11 : ((c * c) * x) * u = ((c * c) * y) * u := by
    clear * - step9
    simp_all only

  have step12 : ((c * c) * x) * u = (c * c) * (x * u) := by
    clear * -
    rw [mul_assoc]

  have step13 : (c * c) * (x * u) = (c * c) * (u * x) := by
    clear * -
    rw [mul_comm x u]

  have step14 : (c * c) * (u * x) = ((c * c) * u) * x := by
    clear * -
    simp only [mul_assoc]

  have step15 : ((c * c) * u) * x = c * x := by
    clear * - step10
    simp_all only

  have step16 : ((c * c) * x) * u = a := by
    clear * - step12 step13 step14 step15 step1
    subst step1
    simp_all only

  have step17 : ((c * c) * y) * u = (c * c) * (y * u) := by
    clear * -
    rw [mul_assoc]

  have step18 : (c * c) * (y * u) = (c * c) * (u * y) := by
    clear * -
    rw [mul_comm y u]

  have step19 : (c * c) * (u * y) = ((c * c) * u) * y := by
    clear * -
    simp only [mul_assoc]

  have step20 : ((c * c) * u) * y = c * y := by
    clear * - step10
    simp_all only

  have step21 : ((c * c) * y) * u = b := by
    clear * - step17 step18 step19 step20 step2
    subst step2
    simp_all only

  have step22 : a = b := by
    clear * - step11 step16 step21
    subst step16 step21
    simp_all only

  exact step22