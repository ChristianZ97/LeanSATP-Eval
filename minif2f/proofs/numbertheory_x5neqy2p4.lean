import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by
  intro h_eq
  have h_mod_eq : (x : ZMod 11) ^ 5 = (y : ZMod 11) ^ 2 + 4 := by
    clear * - h_eq
    (norm_cast at *)
    simp_all only [Int.cast_add, Int.cast_pow, Int.cast_ofNat]

  have h_pow5_set : ∀ z : ZMod 11, z ^ 5 ∈ ({0, 1, 10} : Set (ZMod 11)) := by
    clear * -
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff]
    decide

  have h_sq_set : ∀ z : ZMod 11, z ^ 2 ∈ ({0, 1, 3, 4, 5, 9} : Set (ZMod 11)) := by
    clear * -
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff]
    decide

  have h_rhs_set : ∀ z : ZMod 11, z ^ 2 + 4 ∈ ({2, 4, 5, 7, 8, 9} : Set (ZMod 11)) := by
    clear * - h_sq_set
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, add_left_eq_self]
    intro z
    fin_cases z <;> try simp_all <;> tauto

  have h_disjoint_sets : ({0, 1, 10} : Set (ZMod 11)) ∩ ({2, 4, 5, 7, 8, 9} : Set (ZMod 11)) = ∅ := by
    clear * -
    try apply Set.ext
    simp_all only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and, not_or, forall_eq_or_imp, forall_eq]
    constructor <;> decide <;> norm_num

  have h_x_in_lhs : (x : ZMod 11) ^ 5 ∈ ({0, 1, 10} : Set (ZMod 11)) := by
    clear * - h_pow5_set
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff]

  have h_y_in_rhs : (y : ZMod 11) ^ 2 + 4 ∈ ({2, 4, 5, 7, 8, 9} : Set (ZMod 11)) := by
    clear * - h_rhs_set
    simp_all only [Set.mem_insert_iff, add_left_eq_self, Set.mem_singleton_iff]

  have h_common_value : (x : ZMod 11) ^ 5 ∈ ({2, 4, 5, 7, 8, 9} : Set (ZMod 11)) := by
    clear * - h_mod_eq h_y_in_rhs
    simp_all only [Set.mem_insert_iff, add_left_eq_self, Set.mem_singleton_iff]

  have h_contradiction : False := by
    clear * - h_x_in_lhs h_common_value h_disjoint_sets
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff]
    cases h_x_in_lhs with
    | inl h =>
      cases h_common_value with
      | inl h_1 =>
        simp_all only
        (norm_cast at *)
      | inr h_2 =>
        cases h_2 with
        | inl h_1 =>
          simp_all only
          (norm_cast at *)
        | inr h_3 =>
          cases h_3 with
          | inl h_1 =>
            simp_all only
            (norm_cast at *)
          | inr h_2 =>
            cases h_2 with
            | inl h_1 =>
              simp_all only
              (norm_cast at *)
            | inr h_3 =>
              cases h_3 with
              | inl h_1 =>
                simp_all only
                (norm_cast at *)
              | inr h_2 =>
                simp_all only
                (norm_cast at *)
    | inr h_1 =>
      cases h_common_value with
      | inl h =>
        cases h_1 with
        | inl h_2 =>
          simp_all only
          (norm_cast at *)
        | inr h_3 =>
          simp_all only
          (norm_cast at *)
      | inr h_2 =>
        cases h_1 with
        | inl h =>
          cases h_2 with
          | inl h_1 =>
            simp_all only
            (norm_cast at *)
          | inr h_3 =>
            cases h_3 with
            | inl h_1 =>
              simp_all only
              (norm_cast at *)
            | inr h_2 =>
              cases h_2 with
              | inl h_1 =>
                simp_all only
                (norm_cast at *)
              | inr h_3 =>
                cases h_3 with
                | inl h_1 =>
                  simp_all only
                  (norm_cast at *)
                | inr h_2 =>
                  simp_all only
                  (norm_cast at *)
        | inr h_3 =>
          cases h_2 with
          | inl h =>
            simp_all only
            (norm_cast at *)
          | inr h_1 =>
            cases h_1 with
            | inl h =>
              simp_all only
              (norm_cast at *)
            | inr h_2 =>
              cases h_2 with
              | inl h =>
                simp_all only
                (norm_cast at *)
              | inr h_1 =>
                cases h_1 with
                | inl h =>
                  simp_all only
                  (norm_cast at *)
                | inr h_2 =>
                  simp_all only
                  (norm_cast at *)

  exact False.elim h_contradiction
