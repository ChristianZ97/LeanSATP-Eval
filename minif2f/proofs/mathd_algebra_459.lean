import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_459 (a b c d : ℚ) (h₀ : 3 * a = b + c + d) (h₁ : 4 * b = a + c + d)
    (h₂ : 2 * c = a + b + d) (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 := by
  have h_step5 : 3 * a + a = b + c + d + a := by
    clear * - h₀
    simp_all only

  have h_step6 : 4 * a = a + b + c + d := by
    clear * - h_step5
    simp_all only [add_left_inj]
    (nlinarith)

  have h_step7 : 4 * b + b = a + c + d + b := by
    clear * - h₁
    simp_all only

  have h_step8 : 5 * b = a + b + c + d := by
    clear * - h_step7
    simp_all only [add_left_inj]
    (nlinarith)

  have h_step9 : 2 * c + c = a + b + d + c := by
    clear * - h₂
    simp_all only

  have h_step10 : 3 * c = a + b + c + d := by
    clear * - h_step9
    simp_all only [add_left_inj]
    (nlinarith)

  have h_step11 : 4 * a = 5 * b := by
    clear * - h_step6 h_step8
    simp_all only

  have h_step12 : 5 * b = 3 * c := by
    clear * - h_step8 h_step10
    simp_all only

  have h_step13 : b = (4 : ℚ) / 5 * a := by
    clear * - h_step11
    (field_simp)
    simp_all only
    (nlinarith)

  have h_step14 : c = (5 : ℚ) / 3 * b := by
    clear * - h_step12
    (field_simp)
    simp_all only
    (nlinarith)

  have h_step15 : c = (5 : ℚ) / 3 * ((4 : ℚ) / 5 * a) := by
    clear * - h_step14 h_step13
    subst h_step14 h_step13
    simp_all only

  have h_step16 : c = (4 : ℚ) / 3 * a := by
    clear * - h_step15
    subst h_step15
    (field_simp)
    (nlinarith)

  have h_step17 : 8 * a + 10 * ((4 : ℚ) / 5 * a) + 6 * ((4 : ℚ) / 3 * a) = 24 := by
    clear * - h₃ h_step13 h_step16
    subst h_step16 h_step13
    simp_all only

  have h_step18 : 8 * a + 8 * a + 8 * a = 24 := by
    clear * - h_step17
    (nlinarith)

  have h_step19 : 24 * a = 24 := by
    clear * - h_step18
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀]
    (nlinarith)

  have h_step20 : a = 1 := by
    clear * - h_step19
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀]

  have h_step21 : b = 4 / 5 := by
    clear * - h_step13 h_step20
    subst h_step20 h_step13
    simp_all only [mul_one]

  have h_step22 : c = 4 / 3 := by
    clear * - h_step16 h_step20
    subst h_step16 h_step20
    simp_all only [mul_one]

  have h_step23 : d = 3 * a - b - c := by
    clear * - h₀
    simp_all only
    (nlinarith)

  have h_step24 : d = 3 - 4 / 5 - 4 / 3 := by
    clear * - h_step23 h_step20 h_step21 h_step22
    subst h_step23 h_step21 h_step22 h_step20
    simp_all only [mul_one]

  have h_step25 : d = (45 : ℚ) / 15 - (12 : ℚ) / 15 - (20 : ℚ) / 15 := by
    clear * - h_step24
    subst h_step24
    (field_simp)
    (nlinarith)

  have h_step26 : d = ((45 : ℚ) - (12 : ℚ) - (20 : ℚ)) / 15 := by
    clear * - h_step25
    subst h_step25
    (field_simp)

  have h_step27 : d = (13 : ℚ) / 15 := by
    clear * - h_step26
    subst h_step26
    (field_simp)
    (nlinarith)

  have h_step28 : Nat.gcd 13 15 = 1 := by
    clear * -
    simp_all only [reduceGcd]

  have h_step29 : d.num = (13 : ℤ) := by
    clear * - h_step27 h_step28
    subst h_step27
    simp_all only [reduceGcd]
    (norm_num [*] at *)

  have h_step30 : d.den = (15 : ℕ) := by
    clear * - h_step27 h_step28
    subst h_step27
    simp_all only [reduceGcd]
    (norm_num [*] at *)

  have h_step31 : (↑d.den : ℤ) + d.num = (15 : ℤ) + 13 := by
    clear * - h_step29 h_step30
    simp_all only [Nat.cast_ofNat, Int.reduceAdd]

  have h_step32 : ↑d.den + d.num = 28 := by
    clear * - h_step31
    simp_all only [Int.reduceAdd]

  exact h_step32