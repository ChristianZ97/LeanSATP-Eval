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
    aesop (config := {
      maxRuleApplications := 400
      maxRuleApplicationDepth := 10
      maxNormIterations := 800
      maxGoals := 128
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 100 (by zify))
      (add norm 100 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by ring_nf))
      (add safe 0 (by simp_all))
      (add norm 0 (by grind only [Int.ModEq]))
      (add norm 1 (by field_simp [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime] at *))
      (add norm 0 (by grind only [Int.natCast_mod]))
      (add norm 100 (by rw [← Int.ofNat_emod]))
      (add norm 100 (by rw [← Nat.pow_mod]))
      (add norm 1 (by field_simp [Int.emod_two_eq_zero_or_one] at *))
      (add norm 100 (by rw [← Nat.mul_mod]))
      (add norm 100 (by rw [← Int.emod_two_ne_one]))
      (add norm 100 (by rw [← Nat.mod_two_ne_zero]))
      (add norm 100 (by rw [← Nat.mod_mod]))
      (add norm 100 (by rw [← Nat.mul_mod_mod]))
      (add norm 100 (by rw [← Nat.mod_two_ne_one]))
      (add norm 1 (by field_simp [Int.even_iff] at *))
      (add norm 100 (by rw [← Nat.mul_mod_left]))
      (add norm 100 (by rw [← Nat.gcd.induction]))
      (add safe 1 (by simp_all [Int.emod_zero]))
      (add unsafe 50% (by simp_rw [Int.mul_emod]))
      (add unsafe 50% (by simp_rw [Int.emod_emod]))
      (add unsafe 50% (by simp_rw [Int.emod_emod_of_dvd]))
      (add unsafe 50% (by simp_rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]))
      (add unsafe 50% (by simp_rw [Int.emod_self]))
      (add unsafe 50% (by simp_rw [Int.add_emod]))
      (add unsafe 50% (by unfold Int.dvd_iff_emod_eq_zero))
      (add unsafe 50% (by unfold Int.emod_eq_zero_of_dvd))
      (add unsafe 50% (by simp_rw [ZMod.intCast_mod]))
      (add unsafe 50% (by simp_rw [Int.emod_eq_of_lt]))
      (add unsafe 50% (by simp_rw [Int.mul_emod_right]))
      (add unsafe 50% (by unfold Nat.mod_mod_of_dvd))
      (add unsafe 50% (by simp_rw [Int.emod_neg]))
      (add unsafe 50% (by unfold Int.sq_ne_two_mod_four))
      (add unsafe 10% (by push_cast [Int.odd_iff] at *))
      (add unsafe 50% (by simp_rw [Int.emod_abs]))

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
    aesop (config := {
      maxRuleApplications := 400
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      maxGoals := 1024
      enableUnfold := false
      })
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 100 (by zify))
      (add norm 100 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 1 (by ring_nf))
      (add norm 0 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by simp_all))
      (add norm 1 (by simp only [segment_inter_eq_endpoint_of_linearIndependent_sub]))
      (add norm 1 (by simp_all [Finset.singleton_inter_of_not_mem]))
      (add norm 1 (by simp_all [Finset.shadow_singleton_empty]))
      (add norm 1 (by simp_all [Set.singleton_def]))
      (add norm 100 (by rw [Set.powerset_empty] at *))
      (add norm 100 (by rw [balancedCore_empty] at *))
      (add norm 1 (by simp_all [Finset.singleton_inter_of_mem]))
      (add norm 1 (by field_simp [EuclideanGeometry.inter_eq_singleton_orthogonalProjection] at *))
      (add norm 100 (by rw [Finset.shadow_empty] at *))
      (add norm 100 (by rw [Finpartition.atomise_empty] at *))
      (add norm 1 (by simp_all [LawfulSingleton]))
      (add norm 100 (by rw [MeasureTheory.cylinder_empty] at *))
      (add norm 1 (by simp_all [AList.insert_empty]))
      (add norm 1 (by simp_all [Nat.factoredNumbers_empty]))
      (add safe 1 (by rw [Set.singleton_inter_eq_empty]))
      (add safe 1 (by rw [Set.inter_empty]))
      (add safe 1 (by rw [Set.empty_inter]))
      (add safe 1 (by rw [Set.inter_self]))
      (add safe 1 (by rw [Set.cou_inter_self_right_eq_coe]))
      (add safe 1 (by rw [Set.inter_assoc]))
      (add safe 1 (by rw [Set.singleton_ne_empty]))
      (add safe 1 (by rw [OnePoint.range_coe_inter_infty]))
      (add safe 1 (by rw [balanced_empty]))
      (add safe 1 (by rw [Set.inter_eq_iInter]))
      (add safe 1 (by rw [Set.inter_left_comm]))
      (add safe 1 (by rw [Set.countable_empty]))
      (add safe 1 (by rw [Finset.coe_empty]))
      (add safe 1 (by rw [Set.inter_right_comm]))
      (add safe 1 (by rw [convexHull_empty]))
      (add safe 100 (by simp [segment_inter_eq_endpoint_of_linearIndependent_of_ne] at *))
      (add safe 1 (by rw [Set.mul_empty]))
      (add safe 1 (by rw [Set.iUnion_empty]))

  have h_contradiction : False := by
    clear * - h_mod h_fifth_residues h_shifted_residues h_disjoint_sets
    aesop (config := {
      maxRuleApplications := 400
      maxRuleApplicationDepth := 20
      maxNormIterations := 520
      maxGoals := 256
      useSimpAll := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 0 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by ext))
      (add norm 100 (by exfalso))
      (add norm 0 (by simp_all))
      (add norm 0 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 1 (by zify))
      (add safe 1 (by ring_nf))
      (add safe 0 (by split))
      (add norm 1 (by simp only [Set.mem_singleton_iff]))
      (add norm 1 (by simp_all [Finset.shadow_singleton_empty]))
      (add norm 0 (by grind only [IsEmpty.forall_iff]))
      (add norm 1 (by simp only [Finset.mem_singleton_self]))
      (add safe 1 (by rw [Set.not_mem_empty]))
      (add safe 0 (by nlinarith [Finset.mem_singleton]))
      (add safe 1 (by rw [Set.finite_empty]))
      (add safe 1 (by rw [Set.iUnion_false]))
      (add safe 0 (by nlinarith [False.elim]))
      (add safe 1 (by rw [Finset.coe_empty]))
      (add safe 1 (by rw [Set.inter_empty]))
      (add safe 0 (by simp_all [Set.powerset_empty]))
      (add safe 1 (by rw [Set.iUnion_empty]))
      (add safe 1 (by rw [Finset.filter_False]))
      (add safe 1 (by rw [Language.zero_def]))
      (add safe 0 (by simp_all [ZFSet.sUnion_empty]))
      (add safe 1 (by rw [Set.mul_empty]))
      (add safe 0 (by nlinarith [Finset.mem_insert]))
      (add safe 1 (by rw [Class.not_mem_empty]))
      (add unsafe 90% (by rw [Finset.not_mem_empty]))
      (add unsafe 90% (by rw [Set.mem_empty_iff_false]))
      (add unsafe 90% (by rw [ZFSet.not_mem_empty]))
      (add unsafe 90% (by rw [Set.iInter_false]))
      (add unsafe 90% (by rw [Set.singleton_ne_empty]))
      (add unsafe 90% (by rw [Set.forall_mem_empty]))
      (add unsafe 90% (by rw [Set.image_empty]))
      (add unsafe 90% (by rw [Set.prod_empty]))
      (add unsafe 90% (by rw [Set.countable_empty]))
      (add unsafe 50% (by unfold mul_not_mem_of_exponent_two))
      (add unsafe 90% (by rw [isPreconnected_empty]))
      (add unsafe 90% (by rw [MeasureTheory.cylinder_empty]))
      (add unsafe 90% (by rw [OnePoint.range_coe_inter_infty]))

  exact False.elim h_contradiction
