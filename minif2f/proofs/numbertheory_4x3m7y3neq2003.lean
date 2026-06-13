import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
  intro h_eq

  have h_2003_mod : (2003 : ℤ) % 7 = 1 := by
    clear * -
    simp_all only [Int.reduceMod]

  have h_eq_cong : (4 * x ^ 3 - 7 * y ^ 3) % 7 = (2003 : ℤ) % 7 := by
    clear * - h_eq
    simp_all only [Int.reduceMod]

  have h_7y_div : (7 * y ^ 3) % 7 = 0 := by
    clear * -
    simp_all only [Int.mul_emod_right]

  have h_lhs_cong : (4 * x ^ 3) % 7 = (4 * x ^ 3 - 7 * y ^ 3) % 7 := by
    clear * - h_7y_div
    simp_all only [Int.mul_emod_right]
    (omega)

  have h_4x_cong : (4 * x ^ 3) % 7 = 1 := by
    clear * - h_eq_cong h_lhs_cong h_2003_mod
    simp_all only [Int.reduceMod]

  have h_mult_2_left : (2 * (4 * x ^ 3)) % 7 = (2 * 1 : ℤ) % 7 := by
    clear * - h_4x_cong
    simp_all only [mul_one, Int.reduceMod]
    (omega)

  have h_8_mod_7 : (8 : ℤ) % 7 = 1 := by
    clear * -
    simp_all only [Int.reduceMod]

  have h_x_cubed_cong : (x ^ 3) % 7 = 2 := by
    clear * - h_mult_2_left h_8_mod_7
    simp_all only [mul_one, Int.reduceMod]
    (omega)

  have h_case_0 : (0 : ℤ) ^ 3 % 7 = 0 := by
    clear * -
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, EuclideanDomain.zero_mod]

  have h_case_1 : (1 : ℤ) ^ 3 % 7 = 1 := by
    clear * -
    simp_all only [one_pow, Int.reduceMod]

  have h_case_2 : (2 : ℤ) ^ 3 % 7 = 1 := by
    clear * -
    simp_all only [Int.reducePow, Int.reduceMod]

  have h_case_3 : (3 : ℤ) ^ 3 % 7 = 6 := by
    clear * -
    simp_all only [Int.reducePow, Int.reduceMod]

  have h_case_4 : (4 : ℤ) ^ 3 % 7 = 1 := by
    clear * -
    simp_all only [Int.reducePow, Int.reduceMod]

  have h_case_5 : (5 : ℤ) ^ 3 % 7 = 6 := by
    clear * -
    simp_all only [Int.reducePow, Int.reduceMod]

  have h_case_6 : (6 : ℤ) ^ 3 % 7 = 6 := by
    clear * -
    simp_all only [Int.reducePow, Int.reduceMod]

  have h_residue_set : (x ^ 3) % 7 = 0 ∨ (x ^ 3) % 7 = 1 ∨ (x ^ 3) % 7 = 6 := by
    clear * - h_case_0 h_case_1 h_case_2 h_case_3 h_case_4 h_case_5 h_case_6
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, EuclideanDomain.zero_mod, one_pow,
      Int.reduceMod, Int.reducePow, EuclideanDomain.mod_eq_zero]
    have h1 : x ^ 3 % 7 = (x % 7) ^ 3 % 7
    · simp [pow_succ, Int.mul_emod, Int.ModEq]
    · simp_all only
      have h2 := Int.emod_nonneg x (by decide : (7 : ℤ) ≠ 0)
      have h3 : x % 7 < 7 := Int.emod_lt _ (by norm_num)
      interval_cases h : x % 7 <;> simp_all (config := { decide := true })

  have h_2_not_0 : (2 : ℤ) ≠ 0 := by
    clear * -
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

  have h_2_not_1 : (2 : ℤ) ≠ 1 := by
    clear * -
    simp_all only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]

  have h_2_not_6 : (2 : ℤ) ≠ 6 := by
    clear * -
    simp_all only [ne_eq, OfNat.ofNat_eq_ofNat, reduceEqDiff, not_false_eq_true]

  have h_false : False := by
    clear * - h_x_cubed_cong h_residue_set h_2_not_0 h_2_not_1 h_2_not_6
    simp_all only [OfNat.ofNat_eq_ofNat, reduceEqDiff, or_self]

  exact h_false
