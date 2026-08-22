
import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), n > 0 ∧ a ^ n = 1 := by
  -- Step 1: |G| = N
  have h_card_def : ∃ (N : ℕ), N > 0 ∧ Fintype.card G = N := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [IsPGroup.of_card]))
      (add norm 0 (by grind only [VectorSpace.card_fintype]))
      (add norm 0 (by grind only [Finite.one_lt_card]))
      (add norm 0 (by grind only [exists_pow_ne_one_of_isCyclic]))
      (add norm 0 (by grind only [IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point]))
      (add norm 0 (by grind only [Fintype.card_pos]))
      (add norm 0 (by grind only [Subgroup.index_eq_card]))
      (add norm 0 (by grind only [ConjAct.fixedPoints_eq_center]))
      (add norm 0 (by grind only [Fintype.card_pos_iff]))
      (add norm 0 (by grind only [exists_prime_addOrderOf_dvd_card]))
      (add norm 0 (by grind only [Fintype.card]))
      (add norm 0 (by grind only [Fintype.card_ne_zero]))
      (add norm 0 (by grind only [Fintype.card_units]))
      (add norm 0 (by grind only [Sylow.exists_subgroup_card_pow_prime]))
      (add norm 0 (by grind only [IsPGroup.iff_card]))
      (add norm 0 (by grind only [orderOf_eq_card_of_forall_mem_zpowers]))
      (add norm 0 (by grind only [IsCyclic]))
      (add norm 0 (by grind only [Nat.card_eq_fintype_card]))
      (add norm 0 (by grind only [Subgroup.SchurZassenhausInduction.step7]))
      (add norm 0 (by grind only [Subgroup.card_eq_card_quotient_mul_card_subgroup]))
      (add norm 0 (by grind only [Sylow.directProductOfNormal]))
      (add norm 0 (by grind only [Fintype.one_lt_card_iff_nontrivial]))
      (add norm 0 (by grind only [Finite.card_pos]))
      (add norm 0 (by grind only [Subgroup.fintypeQuotientOfFiniteIndex]))
      (add norm 0 (by grind only [Subgroup.index_ne_zero_of_finite]))
      (add norm 0 (by grind only [IsPGroup.nontrivial_iff_card]))
      (add norm 0 (by grind only [Fintype.exists_pair_of_one_lt_card]))
      (add norm 0 (by grind only [isNilpotent_of_product_of_sylow_group]))
      (add norm 0 (by grind only [GaloisField.card]))
      (add norm 0 (by grind only [Polynomial.Gal.card_of_separable]))
      (add norm 0 (by grind only [Subgroup.one_lt_index_of_ne_top]))
      (add unsafe 10% (by grind only [Fintype.one_lt_card]))

  let N := Classical.choose h_card_def
  have h_N_pos : N > 0 := Classical.choose_spec h_card_def |>.left
  have h_card_eq : Fintype.card G = N := Classical.choose_spec h_card_def |>.right
  -- Step 3: Define the sequence of powers a^1, ..., a^(N+1)
  -- We consider the function f : Fin (N + 1) → G where f i = a ^ (i.val + 1)
  -- Actually, it's easier to work with indices from 1 to N+1 in ℕ
  -- Let's define a list or just use the pigeonhole principle directly on Fin (N+1)
  -- Consider the map from Fin (N + 1) to G given by i ↦ a ^ (i.val + 1)
  -- Since there are N + 1 elements in the domain and only N elements in G,
  -- this map is not injective.
  -- def pow_map (i : Fin (N + 1)) : G := a ^ (i.val + 1)
  -- Step 7: There exist distinct i, j in Fin (N + 1) such that pow_map i = pow_map j
  -- have h_not_injective : ¬Function.Injective pow_map := by
    -- -- The cardinality of Fin (N + 1) is N + 1, which is greater than N.
    -- -- If the map were injective, then the image would have size N + 1.
    -- -- But the codomain G has size N. Contradiction.
    -- intro h_inj
    -- have h_image_size : Fintype.card (Fin (N + 1)) ≤ Fintype.card G := by
      -- apply Fintype.card_le_of_injective
      -- exact h_inj

    -- simp_all [h_card_eq]
    -- <;> omega

  -- From non-injectivity, we get distinct indices i, j with same image
  -- have h_exist_distinct : ∃ (i j : Fin (N + 1)), i ≠ j ∧ pow_map i = pow_map j := by
    -- by_contra h
    -- push_neg at h
    -- -- If no two distinct elements map to the same value, then it's injective
    -- have h_inj : Function.Injective pow_map := by
      -- intro x y hxy
      -- by_cases hxey : x = y
      -- · exact hxey
      -- · exfalso
        -- have h_conflict := h hxey hxy
        -- contradiction

    -- contradiction

  -- rcases h_exist_distinct with ⟨i, j, hij_neq, hij_eq⟩
  -- Step 8 & 9: Assume w.l.o.g. i < j (in terms of natural number values)
  -- i and j are Fin (N + 1). Let ni = i.val, nj = j.val.
  -- ni, nj ∈ {0, ..., N}. The powers are a^(ni+1) and a^(nj+1).
  -- Since i ≠ j, ni ≠ nj.
  -- let ni := i.val
  -- let nj := j.val
  -- have h_ni_range : ni < N + 1 := i.is_lt
  -- have h_nj_range : nj < N + 1 := j.is_lt
  -- WLOG assume ni < nj. If not, swap i and j.
  -- by_cases h_order : ni < nj
  ·
    -- Case: ni < nj
    use N
    constructor
    · exact h_N_pos
    · rw [← h_card_eq]
      apply pow_card_eq_one

  -- ·
    -- -- Case: ni >= nj. Since i ≠ j, we must have ni > nj.
    -- have h_gt : nj < ni := by
      -- by_contra h_le
      -- have h_eq : ni = nj := by
        -- have h_ne : ni ≤ nj := by
          -- contrapose! h_le
          -- omega

        -- omega

      -- have h_fin_eq : i = j := Fin.ext h_eq
      -- contradiction

    -- -- Swap roles of i and j effectively, or just repeat the logic with swapped indices
    -- -- We have a^(ni+1) = a^(nj+1) and nj < ni.
    -- -- Similar derivation leads to a^(ni+1 - (nj+1)) = 1
    -- let k := (ni + 1) - (nj + 1)
    -- have h_k_def : k = (ni + 1) - (nj + 1) := rfl
    -- have h_k_pos : k > 0 := by
      -- have h_lt : nj + 1 < ni + 1 := by omega
      -- omega

    -- have h_int_exponent_eq : (a : G) ^ (((ni + 1 : ℤ) - (nj + 1 : ℤ))) = 1 := by
      -- have h1 : (a : G) ^ (ni + 1 : ℤ) = (a : G) ^ (ni + 1 : ℕ) := by simp
      -- have h2 : (a : G) ^ (nj + 1 : ℤ) = (a : G) ^ (nj + 1 : ℕ) := by simp
      -- have h3 : (a : G) ^ (ni + 1 : ℕ) = (a : G) ^ (nj + 1 : ℕ) := by simpa using hij_eq
      -- have h4 : (a : G) ^ ((ni + 1 : ℤ) - (nj + 1 : ℤ)) =
        -- (a : G) ^ (ni + 1 : ℤ) * (a : G) ^ (-(nj + 1 : ℤ)) := by
        -- rw [pow_sub]
        -- <;> simp_all

      -- have h5 : (a : G) ^ (-(nj + 1 : ℤ)) = ((a : G) ^ (nj + 1 : ℤ))⁻¹ := by
        -- rw [Int.negPow]

      -- have h6 : (a : G) ^ ((ni + 1 : ℤ) - (nj + 1 : ℤ)) =
        -- (a : G) ^ (ni + 1 : ℤ) * ((a : G) ^ (nj + 1 : ℤ))⁻¹ := by
        -- rw [h4, h5]

      -- have h7 : (a : G) ^ (nj + 1 : ℤ) = (a : G) ^ (ni + 1 : ℤ) := by
        -- rw [← h2, ← h1, h3]

      -- rw [h6, h7]
      -- simp [mul_inv_self]

    -- have h_natural_exp : (a : G) ^ (k : ℕ) = 1 := by
      -- have h_cast : (k : ℤ) = (ni + 1 : ℤ) - (nj + 1 : ℤ) := by
        -- rw [h_k_def]
        -- norm_cast

      -- have h_val : (a : G) ^ ((k : ℤ)) = 1 := by
        -- rw [h_cast]
        -- exact h_int_exponent_eq

      -- have h_pos : (k : ℤ) ≥ 0 := by positivity
      -- have h_eq : (a : G) ^ ((k : ℤ)) = (a : G) ^ (k : ℕ) := by
        -- rw [Int.coe_nat_pow]
        -- <;> simp_all

      -- rw [h_eq] at h_val
      -- exact h_val

    -- exact ⟨k, h_k_pos, h_natural_exp⟩
