import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12a_2021_p9 : (∏ k in Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k)) = 3 ^ 128 - 2 ^ 128 := by
  let P := ∏ k in Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k)

  have h_expansion : P = ((2:ℕ)^(1) + (3:ℕ)^(1)) * ((2:ℕ)^(2) + (3:ℕ)^(2)) * ((2:ℕ)^(4) + (3:ℕ)^(4)) * ((2:ℕ)^(8) + (3:ℕ)^(8)) * ((2:ℕ)^(16) + (3:ℕ)^(16)) * ((2:ℕ)^(32) + (3:ℕ)^(32)) * ((2:ℕ)^(64) + (3:ℕ)^(64)) := by
    clear * -
    simp_all only [pow_one, reduceAdd, reducePow, reduceMul, P]
    (bound )

  have h_factor_introduction : P = ((3:ℕ) - (2:ℕ)) * ((2:ℕ)^(1) + (3:ℕ)^(1)) * ((2:ℕ)^(2) + (3:ℕ)^(2)) * ((2:ℕ)^(4) + (3:ℕ)^(4)) * ((2:ℕ)^(8) + (3:ℕ)^(8)) * ((2:ℕ)^(16) + (3:ℕ)^(16)) * ((2:ℕ)^(32) + (3:ℕ)^(32)) * ((2:ℕ)^(64) + (3:ℕ)^(64)) := by
    clear * - h_expansion
    simp_all only [pow_one, reduceAdd, reducePow, reduceMul, reduceSub, one_mul, P]

  have h_identity_1 : ((3:ℕ) - (2:ℕ)) * ((3:ℕ)^(1) + (2:ℕ)^(1)) = (3:ℕ)^(2) - (2:ℕ)^(2) := by
    clear * -
    (omega)

  have h_combined_1 : P = ((3:ℕ)^(2) - (2:ℕ)^(2)) * ((2:ℕ)^(2) + (3:ℕ)^(2)) * ((2:ℕ)^(4) + (3:ℕ)^(4)) * ((2:ℕ)^(8) + (3:ℕ)^(8)) * ((2:ℕ)^(16) + (3:ℕ)^(16)) * ((2:ℕ)^(32) + (3:ℕ)^(32)) * ((2:ℕ)^(64) + (3:ℕ)^(64)) := by
    clear * - h_factor_introduction h_identity_1
    simp_all only [reduceSub, pow_one, reduceAdd, one_mul, reducePow, reduceMul, P]

  have h_identity_2 : ((3:ℕ)^(2) - (2:ℕ)^(2)) * ((3:ℕ)^(2) + (2:ℕ)^(2)) = (3:ℕ)^(4) - (2:ℕ)^(4) := by
    clear * -
    simp_all only [reducePow, reduceSub, reduceAdd, reduceMul]

  have h_combined_2 : P = ((3:ℕ)^(4) - (2:ℕ)^(4)) * ((2:ℕ)^(4) + (3:ℕ)^(4)) * ((2:ℕ)^(8) + (3:ℕ)^(8)) * ((2:ℕ)^(16) + (3:ℕ)^(16)) * ((2:ℕ)^(32) + (3:ℕ)^(32)) * ((2:ℕ)^(64) + (3:ℕ)^(64)) := by
    clear * - h_combined_1 h_identity_2
    simp_all only [reducePow, reduceSub, reduceAdd, reduceMul, P]

  have h_identity_3 : ((3:ℕ)^(4) - (2:ℕ)^(4)) * ((3:ℕ)^(4) + (2:ℕ)^(4)) = (3:ℕ)^(8) - (2:ℕ)^(8) := by
    clear * -
    simp_all only [reducePow, reduceSub, reduceAdd, reduceMul]

  have h_combined_3 : P = ((3:ℕ)^(8) - (2:ℕ)^(8)) * ((2:ℕ)^(8) + (3:ℕ)^(8)) * ((2:ℕ)^(16) + (3:ℕ)^(16)) * ((2:ℕ)^(32) + (3:ℕ)^(32)) * ((2:ℕ)^(64) + (3:ℕ)^(64)) := by
    clear * - h_combined_2 h_identity_3
    simp_all only [reducePow, reduceSub, reduceAdd, reduceMul, P]

  have h_identity_4 : ((3:ℕ)^(8) - (2:ℕ)^(8)) * ((3:ℕ)^(8) + (2:ℕ)^(8)) = (3:ℕ)^(16) - (2:ℕ)^(16) := by
    clear * -
    simp_all only [reducePow, reduceSub, reduceAdd, reduceMul]

  have h_combined_4 : P = ((3:ℕ)^(16) - (2:ℕ)^(16)) * ((2:ℕ)^(16) + (3:ℕ)^(16)) * ((2:ℕ)^(32) + (3:ℕ)^(32)) * ((2:ℕ)^(64) + (3:ℕ)^(64)) := by
    clear * - h_combined_3 h_identity_4
    simp_all only [reducePow, reduceSub, reduceAdd, reduceMul, P]

  have h_identity_5 : ((3:ℕ)^(16) - (2:ℕ)^(16)) * ((3:ℕ)^(16) + (2:ℕ)^(16)) = (3:ℕ)^(32) - (2:ℕ)^(32) := by
    clear * -
    (omega)

  have h_combined_5 : P = ((3:ℕ)^(32) - (2:ℕ)^(32)) * ((2:ℕ)^(32) + (3:ℕ)^(32)) * ((2:ℕ)^(64) + (3:ℕ)^(64)) := by
    clear * - h_combined_4 h_identity_5
    simp_all only [reducePow, reduceSub, reduceAdd, reduceMul, P]

  have h_identity_6 : ((3:ℕ)^(32) - (2:ℕ)^(32)) * ((3:ℕ)^(32) + (2:ℕ)^(32)) = (3:ℕ)^(64) - (2:ℕ)^(64) := by
    clear * -
    (omega)

  have h_combined_6 : P = ((3:ℕ)^(64) - (2:ℕ)^(64)) * ((2:ℕ)^(64) + (3:ℕ)^(64)) := by
    clear * - h_combined_5 h_identity_6
    simp_all only [reducePow, reduceSub, reduceAdd, reduceMul, P]

  have h_identity_7 : ((3:ℕ)^(64) - (2:ℕ)^(64)) * ((3:ℕ)^(64) + (2:ℕ)^(64)) = (3:ℕ)^(128) - (2:ℕ)^(128) := by
    clear * -
    simp_all only [reducePow, reduceSub, reduceAdd, reduceMul]

  have h_final : P = (3:ℕ)^(128) - (2:ℕ)^(128) := by
    clear * - h_combined_6 h_identity_7
    simp_all only [reducePow, reduceSub, reduceAdd, reduceMul, P]

  exact h_final
