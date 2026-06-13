
import Mathlib

set_option maxHeartbeats 0

abbrev putnam_1986_a2_solution : ℕ := 3
theorem putnam_1986_a2
: (Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10 = putnam_1986_a2_solution) := by
  let Y : ℕ := 10 ^ 100
  let y : ℝ := (Y : ℝ)
  let S_sum := ∑ k in Finset.range 200, ((-3 : ℝ) ^ k) * (y ^ (199 - k))
  have h_step2_algebra : y ^ 200 = (y + 3) * S_sum + 3 ^ 200 := by
    clear * -
    simp_all only [Nat.reducePow, Nat.cast_ofNat, y, Y, S_sum]
    (norm_num)

  have h_step3_div : y ^ 200 / (y + 3) = S_sum + 3 ^ 200 / (y + 3) := by
    clear * - h_step2_algebra
    simp_all only [Nat.reducePow, Nat.cast_ofNat, y, Y, S_sum]
    (field_simp)
    (nlinarith)

  have h_step4_power : (3 : ℝ) ^ 200 = 9 ^ 100 := by
    clear * -
    (ring)

  have h_step5_ineq : (9 : ℝ) ^ 100 < 10 ^ 100 + 3 := by
    clear * -
    (bound )

  have h_step6_bounds : 0 < (3 : ℝ) ^ 200 / (y + 3) ∧ (3 : ℝ) ^ 200 / (y + 3) < 1 := by
    clear * - h_step4_power h_step5_ineq
    simp_all only [Nat.reducePow, Nat.cast_ofNat, Nat.ofNat_pos, pow_pos, div_pos_iff_of_pos_left, y, Y]
    apply And.intro
    · (nlinarith)
    · (nlinarith)

  let S_int : ℤ := ∑ k in Finset.range 200, ((-3 : ℤ) ^ k) * (Y ^ (199 - k) : ℤ)
  have h_sum_is_int : (S_int : ℝ) = S_sum := by
    clear * -
    simp_all only [Int.reduceNeg, Nat.reducePow, Nat.cast_ofNat, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_ofNat, S_int, Y, S_sum, y]

  have h_S_int_nn : 0 ≤ S_int := by
    clear * - h_step2_algebra h_sum_is_int
    simp_all only [Nat.reducePow, Nat.cast_ofNat, Int.reduceNeg, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_ofNat, y, Y, S_sum, S_int]
    (norm_num [*] at *)

  have h_step7_floor : Nat.floor (y ^ 200 / (y + 3)) = S_int.natAbs := by
    clear * - h_step3_div h_step6_bounds h_sum_is_int h_S_int_nn
    simp_all only [Nat.reducePow, Nat.cast_ofNat, Nat.ofNat_pos, pow_pos, div_pos_iff_of_pos_left, Int.reduceNeg,
      Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_ofNat, y, Y, S_sum, S_int]
    norm_num [Nat.floor_eq_iff]

  have h_expr_match : (10 ^ 20000 : ℝ) / (10 ^ 100 + 3) = y ^ 200 / (y + 3) := by
    clear * -
    simp_all only [Nat.reducePow, Nat.cast_ofNat, y, Y]
    (norm_num)

  have h_Y_mod_10 : (Y : ZMod 10) = 0 := by
    clear * -
    simp_all only [Nat.reducePow, Nat.cast_ofNat, Y]
    rfl

  have h_S_mod_10 : (S_int : ZMod 10) = 3 := by
    clear * - h_Y_mod_10
    simp_all only [Nat.reducePow, Nat.cast_ofNat, Int.reduceNeg, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_ofNat, Y, S_int]
    (norm_num [*] at *)
    rfl

  have h_step_final_mod : S_int.natAbs % 10 = 3 := by
    clear * - h_S_mod_10 h_S_int_nn
    simp_all only [Int.reduceNeg, Nat.reducePow, Nat.cast_ofNat, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_ofNat, S_int, Y]
    (norm_num [*] at *)

  have h_result : Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10 = 3 := by
    calc
      Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10
      = Nat.floor (y ^ 200 / (y + 3)) % 10 := by
        simp_all only [Nat.reducePow, Nat.cast_ofNat, Nat.ofNat_pos, pow_pos, div_pos_iff_of_pos_left, Int.reduceNeg,
            Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_ofNat, y, Y, S_sum, S_int]

      _ = S_int.natAbs % 10 := by
        rw [h_step7_floor]

      _ = 3 := by
        exact h_step_final_mod

  rw [h_result]
