import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by
  intro h_eq

  have h_mod : (x ^ 5 : ℤ) % 11 = (y ^ 2 + 4 : ℤ) % 11 := by
    clear * - h_eq
    simp_all only

  have h_fifth_residues : (x ^ 5) % 11 ∈ ({0, 1, 10} : Set ℤ) := by
    clear * -
    simp [pow_succ, Int.mul_emod]
    have h₁ := Int.emod_nonneg x (by norm_num : (11 : ℤ) ≠ 0)
    have h₂ : x % 11 < 11 := Int.emod_lt _ (by norm_num)
    interval_cases x % 11 <;> simp [mul_assoc]

  have h_square_residues : (y ^ 2) % 11 ∈ ({0, 1, 3, 4, 5, 9} : Set ℤ) := by
    clear * -
    have aux₁ := Int.emod_nonneg y (by norm_num : (11 : ℤ) ≠ 0)
    have aux₂ : y % 11 < 11 := Int.emod_lt_of_pos y (by decide)
    interval_cases h : y % 11 <;> simp [pow_two, Int.mul_emod, Int.add_emod, h] <;> omega

  have h_shifted_residues : (y ^ 2 + 4) % 11 ∈ ({2, 4, 5, 7, 8, 9} : Set ℤ) := by
    clear * - h_square_residues
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
    all_goals omega

  have h_disjoint_sets : ({0, 1, 10} : Set ℤ) ∩ ({2, 4, 5, 7, 8, 9} : Set ℤ) = ∅ := by
    clear * -
    (ext)
    simp_all only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and, not_or]
    intro a
    (omega)

  have h_contradiction : False := by
    clear * - h_mod h_fifth_residues h_shifted_residues h_disjoint_sets
    simp only [Set.mem_insert_iff, EuclideanDomain.mod_eq_zero, Set.mem_singleton_iff] at *
    (omega)

  exact False.elim h_contradiction
