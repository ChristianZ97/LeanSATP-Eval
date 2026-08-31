import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
  intro h_eq
  have h_step2 : (4 * x ^ 3 - 7 * y ^ 3) % 7 = (2003 : ℤ) % 7 := by
    clear * - h_eq
    simp_all only [Int.reduceMod]

  have h_step3 : (7 * y ^ 3) % 7 = 0 := by
    clear * -
    simp_all only [Int.mul_emod_right]

  have h_step4 : (4 * x ^ 3) % 7 = (2003 : ℤ) % 7 := by
    clear * - h_step2 h_step3
    simp_all only [Int.sub_mul_emod_self_left, Int.reduceMod, Int.mul_emod_right]

  have h_step5 : (2003 : ℤ) = 286 * 7 + 1 := by
    clear * -
    simp_all only [Int.reduceMul, Int.reduceAdd]

  have h_step6 : (2003 : ℤ) % 7 = 1 := by
    clear * - h_step5
    simp_all only [Int.reduceMul, Int.reduceAdd, Int.reduceMod]

  have h_step7 : (4 * x ^ 3) % 7 = 1 := by
    clear * - h_step4 h_step6
    simp_all only [Int.reduceMod]

  have h_step8 : (2 * (4 * x ^ 3)) % 7 = (2 * 1) % 7 := by
    clear * - h_step7
    simp_all only [mul_one, Int.reduceMod]
    (omega)

  have h_step9 : (8 * x ^ 3) % 7 = 2 % 7 := by
    clear * - h_step8
    simp_all only [mul_one, Int.reduceMod]
    (omega)

  have h_step10 : 8 % 7 = 1 := by
    clear * -
    simp_all only [reduceMod]

  have h_step11 : (x ^ 3) % 7 = 2 := by
    clear * - h_step9 h_step10
    simp_all only [Int.reduceMod, reduceMod]
    (grind only [Int.ModEq])

  have h_c0 : (0 : ℤ) ^ 3 = 0 := by
    clear * -
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

  have h_mod0 : 0 % 7 = 0 := by
    clear * - h_c0
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mod]

  have h_c1 : (1 : ℤ) ^ 3 = 1 := by
    clear * -
    simp only [one_pow] at *

  have h_mod1 : 1 % 7 = 1 := by
    clear * - h_c1
    simp_all only [one_pow, one_mod]

  have h_c2 : (2 : ℤ) ^ 3 = 8 := by
    clear * -
    simp_all only [Int.reducePow]

  have h_mod2 : 8 % 7 = 1 := by
    clear * - h_c2
    simp_all only [Int.reducePow, reduceMod]

  have h_c3 : (3 : ℤ) ^ 3 = 27 := by
    clear * -
    simp_all only [Int.reducePow]

  have h_c3_dec : (27 : ℤ) = 3 * 7 + 6 := by
    clear * -
    simp_all only [Int.reduceMul, Int.reduceAdd]

  have h_mod3 : 27 % 7 = 6 := by
    clear * - h_c3_dec
    simp_all only [Int.reduceMul, Int.reduceAdd, reduceMod]

  have h_c4 : (4 : ℤ) ^ 3 = 64 := by
    clear * -
    simp_all only [Int.reducePow]

  have h_c4_dec : (64 : ℤ) = 9 * 7 + 1 := by
    clear * -
    simp_all only [Int.reduceMul, Int.reduceAdd]

  have h_mod4 : 64 % 7 = 1 := by
    clear * - h_c4_dec
    simp_all only [Int.reduceMul, Int.reduceAdd, reduceMod]

  have h_c5 : (5 : ℤ) ^ 3 = 125 := by
    clear * -
    simp only [Int.reducePow] at *

  have h_c5_dec : (125 : ℤ) = 17 * 7 + 6 := by
    clear * -
    simp_all only [Int.reduceMul, Int.reduceAdd]

  have h_mod5 : 125 % 7 = 6 := by
    clear * - h_c5_dec
    simp_all only [Int.reduceMul, Int.reduceAdd, reduceMod]

  have h_c6 : (6 : ℤ) ^ 3 = 216 := by
    clear * -
    simp_all only [Int.reducePow]

  have h_c6_dec : (216 : ℤ) = 30 * 7 + 6 := by
    clear * -
    simp_all only [Int.reduceMul, Int.reduceAdd]

  have h_mod6 : 216 % 7 = 6 := by
    clear * - h_c6_dec
    simp_all only [Int.reduceMul, Int.reduceAdd, reduceMod]

  have h_residues : (x ^ 3) % 7 ∈ ({0, 1, 6} : Set ℤ) := by
    clear * - h_mod0 h_mod1 h_mod2 h_mod3 h_mod4 h_mod5 h_mod6
    simp [pow_three, Int.mul_emod, h_mod0, h_mod1, h_mod2, h_mod3, h_mod4, h_mod5, h_mod6]
    have hx := Int.emod_nonneg x (by decide : (7 : ℤ) ≠ 0)
    have h : x % 7 < 7 := Int.emod_lt _ (by omega)
    interval_cases hx : x % 7 <;> simp [*, Int.mul_emod, Int.add_emod, Int.emod_emod]

  have h_not_in : (2 : ℤ) ∉ ({0, 1, 6} : Set ℤ) := by
    clear * -
    simp_all only [Set.mem_insert_iff, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Set.mem_singleton_iff, OfNat.ofNat_eq_ofNat, reduceEqDiff, or_self, not_false_eq_true]

  have h_false : False := by
    clear * - h_step11 h_residues h_not_in
    exact h_not_in $ h_step11 ▸ h_residues

  exact h_false
