
import Mathlib

open Finset

set_option maxHeartbeats 0

abbrev putnam_2025_b3_solution : Prop := ∀ S : Set ℕ,
    S.Nonempty →
    (∀ n ∈ S, 0 < n) →
    (∀ n ∈ S, ∀ d : ℕ, 0 < d → d ∣ (2025 ^ n - 15 ^ n) → d ∈ S) →
    S = {n : ℕ | 0 < n}

theorem putnam_2025_b3 :
    putnam_2025_b3_solution ↔
    ∀ S : Set ℕ,
      S.Nonempty →
      (∀ n ∈ S, 0 < n) →
      (∀ n ∈ S, ∀ d : ℕ, 0 < d → d ∣ (2025 ^ n - 15 ^ n) → d ∈ S) →
      S = {n : ℕ | 0 < n} := by
  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 100 (by simp_all))
    (add norm 1 (by field_simp [*] at *))
    (add norm 1 (by norm_num [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by push_neg))
    (add safe 100 (by interval_cases))
    (add safe 100 (by ring_nf))
    (add safe 0 (by split))
    (add safe 1 (by ring_nf at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Pell.Solution₁.y_ne_zero_of_one_lt_x]))
    (add norm 0 (by grind only [Nat.find_pos]))
    (add norm 0 (by grind only [Nat.sInf_def]))
    (add norm 0 (by grind only [FermatLastTheoremForThreeGen.Solution]))
    (add norm 0 (by grind only [lowerCentralSeries_length_eq_nilpotencyClass]))
    (add norm 0 (by grind only [FermatLastTheoremForThreeGen.Solution.exists_minimal]))
    (add norm 0 (by grind only [Nat.find_min']))
    (add norm 0 (by grind only [least_descending_central_series_length_eq_nilpotencyClass]))
    (add norm 0 (by grind only [Pell.Solution₁.d_pos_of_one_lt_x]))
    (add norm 0 (by grind only [Nat.find]))
    (add norm 0 (by grind only [Pell.IsFundamental.eq_pow_of_nonneg]))
    (add norm 0 (by grind only [preimage_find_eq_disjointed]))
    (add norm 0 (by grind only [Pell.Solution₁.exists_pos_variant]))
    (add norm 0 (by grind only [Nat.find_le]))
    (add norm 0 (by grind only [least_ascending_central_series_length_eq_nilpotencyClass]))
    (add norm 0 (by grind only [Nat.find_mono]))
    (add norm 0 (by grind only [Nat.find_eq_iff]))
    (add norm 0 (by grind only [PNat.le_find_iff]))
    (add norm 0 (by grind only [Nat.find_spec]))
    (add norm 0 (by grind only [Nat.find_le_iff]))
    (add norm 0 (by grind only [Nat.le_find_iff]))
    (add norm 0 (by grind only [Nat.find_lt_iff]))
    (add norm 0 (by grind only [Pell.Solution₁]))
    (add norm 0 (by grind only [Pell.pos_generator_iff_fundamental]))
    (add norm 0 (by grind only [Classical.decPred]))
    (add norm 0 (by grind only [PNat.find_spec]))
    (add norm 0 (by grind only [Group.nilpotencyClass]))
    (add norm 0 (by grind only [Measurable.find]))
    (add norm 0 (by grind only [exists_nat_pow_near]))
    (add norm 0 (by grind only [PNat.find_mono]))
    (add norm 0 (by grind only [PNat.lt_add_one_iff]))
    (add norm 0 (by grind only [upperCentralSeries_eq_top_iff_nilpotencyClass_le]))
