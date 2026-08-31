import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) : Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  have h_a0 : d 0 % 2 = 0 := by
    clear * - h₀
    simp_all only [zero_mod]

  have h_a1 : d 1 % 2 = 0 := by
    clear * - h₁
    simp_all only [zero_mod]

  have h_a2 : d 2 % 2 = 1 := by
    clear * - h₂
    simp_all only [mod_succ]

  have h_d3 : d 3 = d 2 + d 0 := by
    clear * - h₃
    simp_all only [ge_iff_le, le_refl, Nat.add_one_sub_one, tsub_self, Nat.add_left_cancel_iff]

  have h_a3 : d 3 % 2 = 1 := by
    clear * - h_d3 h_a2 h_a0
    simp_all only
    (omega)

  have h_d4 : d 4 = d 3 + d 1 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a4 : d 4 % 2 = 1 := by
    clear * - h_d4 h_a3 h_a1
    simp_all only
    (omega)

  have h_d5 : d 5 = d 4 + d 2 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a5 : d 5 % 2 = 0 := by
    clear * - h_d5 h_a4 h_a2
    simp_all only
    (omega)

  have h_d6 : d 6 = d 5 + d 3 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a6 : d 6 % 2 = 1 := by
    clear * - h_d6 h_a5 h_a3
    simp_all only
    (omega)

  have h_d7 : d 7 = d 6 + d 4 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a7 : d 7 % 2 = 0 := by
    clear * - h_d7 h_a6 h_a4
    simp_all only
    (omega)

  have h_d8 : d 8 = d 7 + d 5 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a8 : d 8 % 2 = 0 := by
    clear * - h_d8 h_a7 h_a5
    simp_all only
    (omega)

  have h_d9 : d 9 = d 8 + d 6 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a9 : d 9 % 2 = 1 := by
    clear * - h_d9 h_a8 h_a6
    simp_all only
    (omega)

  have h_d10 : d 10 = d 9 + d 7 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a10 : d 10 % 2 = 1 := by
    clear * - h_d10 h_a9 h_a7
    simp_all only
    (omega)

  have h_d11 : d 11 = d 10 + d 8 := by
    clear * - h₃
    simp only [ge_iff_le] at *
    (bound )

  have h_a11 : d 11 % 2 = 1 := by
    clear * - h_d11 h_a10 h_a8
    simp_all only
    (omega)

  have h_d12 : d 12 = d 11 + d 9 := by
    clear * - h₃
    simp only [ge_iff_le] at *
    (bound )

  have h_a12 : d 12 % 2 = 0 := by
    clear * - h_d12 h_a11 h_a9
    simp_all only
    (omega)

  have h_d13 : d 13 = d 12 + d 10 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a13 : d 13 % 2 = 1 := by
    clear * - h_d13 h_a12 h_a10
    simp_all only
    (omega)

  have h_d14 : d 14 = d 13 + d 11 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a14 : d 14 % 2 = 0 := by
    clear * - h_d14 h_a13 h_a11
    simp_all only
    (omega)

  have h_d15 : d 15 = d 14 + d 12 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a15 : d 15 % 2 = 0 := by
    clear * - h_d15 h_a14 h_a12
    simp_all only
    (omega)

  have h_d16 : d 16 = d 15 + d 13 := by
    clear * - h₃
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, Nat.add_left_cancel_iff]

  have h_a16 : d 16 % 2 = 1 := by
    clear * - h_d16 h_a15 h_a13
    simp_all only
    (omega)

  have h_period : ∀ n, d (n + 14) % 2 = d n % 2 := by
    clear * - h_a0 h_a1 h_a2 h_a14 h_a15 h_a16 h₃
    intro n
    simp_all only [ge_iff_le, reduceLeDiff, Nat.add_one_sub_one, le_refl, tsub_self, reduceSub, le_add_iff_nonneg_left, _root_.zero_le, add_tsub_cancel_right, reduceSubDiff]
    (omega)

  have h_2021_div : 2021 = (14 : ℕ) * 144 + 5 := by
    clear * -
    simp_all only [reduceMul, reduceAdd]

  have h_2022_div : 2022 = (14 : ℕ) * 144 + 6 := by
    clear * -
    simp_all only [reduceMul, reduceAdd]

  have h_2023_div : 2023 = (14 : ℕ) * 144 + 7 := by
    clear * -
    simp_all only [reduceMul, reduceAdd]

  have h_d2021_mod : d 2021 % 2 = d 5 % 2 := by
    clear * - h_period h_2021_div
    simp_all only [reduceMul, reduceAdd]

  have h_d2021_is_a5 : d 2021 % 2 = 0 := by
    clear * - h_d2021_mod h_a5
    simp_all only

  have h_even_2021 : Even (d 2021) := by
    clear * - h_d2021_is_a5
    (grind only [Nat.even_iff])

  have h_d2022_mod : d 2022 % 2 = d 6 % 2 := by
    clear * - h_period h_2022_div
    simp_all only [reduceMul, reduceAdd]

  have h_d2022_is_a6 : d 2022 % 2 = 1 := by
    clear * - h_d2022_mod h_a6
    simp_all only

  have h_odd_2022 : Odd (d 2022) := by
    clear * - h_d2022_is_a6
    (grind only [Nat.odd_iff])

  have h_d2023_mod : d 2023 % 2 = d 7 % 2 := by
    clear * - h_period h_2023_div
    simp_all only [reduceMul, reduceAdd]

  have h_d2023_is_a7 : d 2023 % 2 = 0 := by
    clear * - h_d2023_mod h_a7
    simp_all only

  have h_even_2023 : Even (d 2023) := by
    clear * - h_d2023_is_a7
    (grind only [Nat.even_iff])

  exact ⟨h_even_2021, h_odd_2022, h_even_2023⟩
