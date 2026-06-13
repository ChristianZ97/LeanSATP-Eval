import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem induction_prod1p1onk3le3m1onn (n : ℕ) (h₀ : 0 < n) :
  (∏ k in Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3)) ≤ (3 : ℝ) - 1 / ↑n := by
  let P : ℕ → ℝ := fun n ↦ ∏ k in Finset.Icc 1 n, (1 + (1 : ℝ) / (k : ℝ) ^ 3)
  let B : ℕ → ℝ := fun n ↦ (3 : ℝ) - 1 / (n : ℝ)
  have h_induction : ∀ (m : ℕ), 0 < m → P m ≤ B m := by
    intro m hm
    induction' hm with m hm IH
    · -- Base case: m = 1
      have h_p1 : P 1 = 2 := by
        aesop (config := {
        maxNormIterations       := 120
        })
        (add safe 4 (by field_simp))
        (add safe 4 (by push_neg))
        (add unsafe 100% (by nlinarith))
        (add unsafe 100% (by simp_all))
        (add unsafe 90% (by field_simp [*] at *))
        (add unsafe 90% (by norm_num [*] at *))
        (add unsafe 80% (by gcongr))
        (add unsafe 80% (by linarith))
        (add unsafe 70% (by bound))
        (add unsafe 70% (by norm_cast at *))
        (add unsafe 70% (by omega))
        (add unsafe 70% (by positivity))
        (add unsafe 70% (by ring_nf at *))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_b1 : B 1 = 2 := by
        aesop (config := {
        maxNormIterations       := 120
        })
        (add safe 4 (by field_simp))
        (add safe 4 (by push_neg))
        (add unsafe 100% (by nlinarith))
        (add unsafe 100% (by simp_all))
        (add unsafe 90% (by field_simp [*] at *))
        (add unsafe 90% (by norm_num [*] at *))
        (add unsafe 80% (by gcongr))
        (add unsafe 80% (by linarith))
        (add unsafe 70% (by bound))
        (add unsafe 70% (by norm_cast at *))
        (add unsafe 70% (by omega))
        (add unsafe 70% (by positivity))
        (add unsafe 70% (by ring_nf at *))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_base : P 1 ≤ B 1 := by
        clear * - h_p1 h_b1
        aesop (config := {
        maxNormIterations       := 120
        })
        (add safe 4 (by field_simp))
        (add safe 4 (by push_neg))
        (add unsafe 100% (by nlinarith))
        (add unsafe 100% (by simp_all))
        (add unsafe 90% (by field_simp [*] at *))
        (add unsafe 90% (by norm_num [*] at *))
        (add unsafe 80% (by gcongr))
        (add unsafe 80% (by linarith))
        (add unsafe 70% (by bound))
        (add unsafe 70% (by norm_cast at *))
        (add unsafe 70% (by omega))
        (add unsafe 70% (by positivity))
        (add unsafe 70% (by ring_nf at *))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      exact h_base

    · -- Inductive step: assume P(m) ≤ B(m), prove P(m+1) ≤ B(m+1)
      have h_ih : P m ≤ B m := IH
      have h_rec_def : P (m + 1) = P m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) := by
        have h1 : P (m + 1) = ∏ k in Finset.Icc 1 (m + 1), (1 + (1 : ℝ) / (k : ℝ) ^ 3) := rfl
        have h2 : P m = ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / (k : ℝ) ^ 3) := rfl
        have h3 : Finset.Icc 1 (m + 1) = Finset.Icc 1 m ∪ {m + 1} := by
          clear * -
          aesop (config := {
          maxNormIterations       := 120
          })
          (add safe 4 (by field_simp))
          (add safe 4 (by push_neg))
          (add unsafe 100% (by nlinarith))
          (add unsafe 100% (by simp_all))
          (add unsafe 90% (by field_simp [*] at *))
          (add unsafe 90% (by norm_num [*] at *))
          (add unsafe 80% (by gcongr))
          (add unsafe 80% (by linarith))
          (add unsafe 70% (by bound))
          (add unsafe 70% (by norm_cast at *))
          (add unsafe 70% (by omega))
          (add unsafe 70% (by positivity))
          (add unsafe 70% (by ring_nf at *))
          (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
          (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
          (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

        have h4 : (∏ k in Finset.Icc 1 (m + 1), (1 + (1 : ℝ) / (k : ℝ) ^ 3)) = (∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / (k : ℝ) ^ 3)) * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) := by
          clear * - h3
          simp_all only [one_div]
          rw [Finset.prod_union]
          · simp_all only [Finset.prod_singleton, Nat.cast_add, Nat.cast_one]
          ·
            simp_all only [Finset.disjoint_singleton_right, Finset.mem_Icc, le_add_iff_nonneg_left, _root_.zero_le,
              add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, and_false, not_false_eq_true]

        clear * - h1 h2 h4
        aesop (config := {
        maxNormIterations       := 120
        })
        (add safe 4 (by field_simp))
        (add safe 4 (by push_neg))
        (add unsafe 100% (by nlinarith))
        (add unsafe 100% (by simp_all))
        (add unsafe 90% (by field_simp [*] at *))
        (add unsafe 90% (by norm_num [*] at *))
        (add unsafe 80% (by gcongr))
        (add unsafe 80% (by linarith))
        (add unsafe 70% (by bound))
        (add unsafe 70% (by norm_cast at *))
        (add unsafe 70% (by omega))
        (add unsafe 70% (by positivity))
        (add unsafe 70% (by ring_nf at *))
        (add unsafe 30% (by first | apply LieAlgebra.IsSemisimple.isSimple_of_isAtom | rw [LieAlgebra.IsSemisimple.isSimple_of_isAtom] | simp only [LieAlgebra.IsSemisimple.isSimple_of_isAtom]))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_step1 : P (m + 1) ≤ B m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) := by
        have h1 : P (m + 1) = P m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) := h_rec_def
        have h2 : P m ≤ B m := h_ih
        have h3 : (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) ≥ 0 := by
          have h_pos : ((m + 1) : ℝ) > 0 := by
            clear * - hm
            aesop (config := {
            maxNormIterations       := 120
            })
            (add safe 4 (by field_simp))
            (add safe 4 (by push_neg))
            (add unsafe 100% (by nlinarith))
            (add unsafe 100% (by simp_all))
            (add unsafe 90% (by field_simp [*] at *))
            (add unsafe 90% (by norm_num [*] at *))
            (add unsafe 80% (by gcongr))
            (add unsafe 80% (by linarith))
            (add unsafe 70% (by bound))
            (add unsafe 70% (by norm_cast at *))
            (add unsafe 70% (by omega))
            (add unsafe 70% (by positivity))
            (add unsafe 70% (by ring_nf at *))
            (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
            (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

          have h_pow_pos : ((m + 1) : ℝ) ^ 3 > 0 := by
            clear * - h_pos
            aesop (config := {
            maxNormIterations       := 120
            })
            (add safe 4 (by field_simp))
            (add safe 4 (by push_neg))
            (add unsafe 100% (by nlinarith))
            (add unsafe 100% (by simp_all))
            (add unsafe 90% (by field_simp [*] at *))
            (add unsafe 90% (by norm_num [*] at *))
            (add unsafe 80% (by gcongr))
            (add unsafe 80% (by linarith))
            (add unsafe 70% (by bound))
            (add unsafe 70% (by norm_cast at *))
            (add unsafe 70% (by omega))
            (add unsafe 70% (by positivity))
            (add unsafe 70% (by ring_nf at *))
            (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
            (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

          clear * - h_pos h_pow_pos
          aesop (config := {
          maxNormIterations       := 120
          })
          (add safe 4 (by field_simp))
          (add safe 4 (by push_neg))
          (add unsafe 100% (by nlinarith))
          (add unsafe 100% (by simp_all))
          (add unsafe 90% (by field_simp [*] at *))
          (add unsafe 90% (by norm_num [*] at *))
          (add unsafe 80% (by gcongr))
          (add unsafe 80% (by linarith))
          (add unsafe 70% (by bound))
          (add unsafe 70% (by norm_cast at *))
          (add unsafe 70% (by omega))
          (add unsafe 70% (by positivity))
          (add unsafe 70% (by ring_nf at *))
          (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
          (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

        clear * - h1 h2 h3
        simp_all only [one_div, ge_iff_le, P, B]
        gcongr

      have h_expand : B m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) = 3 + 3 / ((m + 1) : ℝ) ^ 3 - 1 / (m : ℝ) - 1 / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) := by
        have h1 : B m = (3 : ℝ) - 1 / (m : ℝ) := rfl
        have h2 : (3 : ℝ) - 1 / (m : ℝ) = (3 : ℝ) + 0 - 1 / (m : ℝ) := by
          clear * -
          aesop (config := {
          maxNormIterations       := 120
          })
          (add safe 4 (by field_simp))
          (add safe 4 (by push_neg))
          (add unsafe 100% (by nlinarith))
          (add unsafe 100% (by simp_all))
          (add unsafe 90% (by field_simp [*] at *))
          (add unsafe 90% (by norm_num [*] at *))
          (add unsafe 80% (by gcongr))
          (add unsafe 80% (by linarith))
          (add unsafe 70% (by bound))
          (add unsafe 70% (by norm_cast at *))
          (add unsafe 70% (by omega))
          (add unsafe 70% (by positivity))
          (add unsafe 70% (by ring_nf at *))
          (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
          (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

        clear * - h1 h2
        simp_all only [one_div, add_zero, mul_inv_rev, B]
        induction m <;> field_simp <;> ring

      have h_key_ineq : 3 + 3 / ((m + 1) : ℝ) ^ 3 - 1 / (m : ℝ) - 1 / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) ≤ 3 - 1 / ((m + 1) : ℝ) := by
        have h1 : 3 / ((m + 1) : ℝ) ^ 3 - 1 / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) ≤ 1 / (m : ℝ) - 1 / ((m + 1) : ℝ) := by
          have h2 : 3 / ((m + 1) : ℝ) ^ 3 - 1 / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) = (3 * (m : ℝ) - 1) / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) := by
            clear * - hm
            aesop (config := {
            maxNormIterations       := 120
            })
            (add safe 4 (by field_simp))
            (add safe 4 (by push_neg))
            (add unsafe 100% (by nlinarith))
            (add unsafe 100% (by simp_all))
            (add unsafe 90% (by field_simp [*] at *))
            (add unsafe 90% (by norm_num [*] at *))
            (add unsafe 80% (by gcongr))
            (add unsafe 80% (by linarith))
            (add unsafe 70% (by bound))
            (add unsafe 70% (by norm_cast at *))
            (add unsafe 70% (by omega))
            (add unsafe 70% (by positivity))
            (add unsafe 70% (by ring_nf at *))
            (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
            (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
            (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

          have h3 : 1 / (m : ℝ) - 1 / ((m + 1) : ℝ) = 1 / ((m : ℝ) * ((m + 1) : ℝ)) := by
            clear * - hm
            aesop (config := {
            maxNormIterations       := 120
            })
            (add safe 4 (by field_simp))
            (add safe 4 (by push_neg))
            (add unsafe 100% (by nlinarith))
            (add unsafe 100% (by simp_all))
            (add unsafe 90% (by field_simp [*] at *))
            (add unsafe 90% (by norm_num [*] at *))
            (add unsafe 80% (by gcongr))
            (add unsafe 80% (by linarith))
            (add unsafe 70% (by bound))
            (add unsafe 70% (by norm_cast at *))
            (add unsafe 70% (by omega))
            (add unsafe 70% (by positivity))
            (add unsafe 70% (by ring_nf at *))
            (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
            (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
            (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

          have h4 : (3 * (m : ℝ) - 1) / ((m : ℝ) * ((m + 1) : ℝ) ^ 3) ≤ 1 / ((m : ℝ) * ((m + 1) : ℝ)) := by
            have h5 : 3 * (m : ℝ) - 1 ≤ ((m + 1) : ℝ) ^ 2 := by
              have h6 : 0 ≤ ((m : ℝ) - 1/2 : ℝ) ^ 2 + 7/4 := by
                clear * -
                aesop (config := {
                maxNormIterations       := 120
                })
                (add safe 4 (by field_simp))
                (add safe 4 (by push_neg))
                (add unsafe 100% (by nlinarith))
                (add unsafe 100% (by simp_all))
                (add unsafe 90% (by field_simp [*] at *))
                (add unsafe 90% (by norm_num [*] at *))
                (add unsafe 80% (by gcongr))
                (add unsafe 80% (by linarith))
                (add unsafe 70% (by bound))
                (add unsafe 70% (by norm_cast at *))
                (add unsafe 70% (by omega))
                (add unsafe 70% (by positivity))
                (add unsafe 70% (by ring_nf at *))
                (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
                (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
                (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

              have h7 : ((m : ℝ) - 1/2 : ℝ) ^ 2 + 7/4 = (m : ℝ) ^ 2 - (m : ℝ) + 2 := by
                clear * -
                aesop (config := {
                maxNormIterations       := 120
                })
                (add safe 4 (by field_simp))
                (add safe 4 (by push_neg))
                (add unsafe 100% (by nlinarith))
                (add unsafe 100% (by simp_all))
                (add unsafe 90% (by field_simp [*] at *))
                (add unsafe 90% (by norm_num [*] at *))
                (add unsafe 80% (by gcongr))
                (add unsafe 80% (by linarith))
                (add unsafe 70% (by bound))
                (add unsafe 70% (by norm_cast at *))
                (add unsafe 70% (by omega))
                (add unsafe 70% (by positivity))
                (add unsafe 70% (by ring_nf at *))
                (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
                (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

              have h8 : (m : ℝ) ^ 2 - (m : ℝ) + 2 ≥ 0 := by
                clear * - h6 h7
                aesop (config := {
                maxNormIterations       := 120
                })
                (add safe 4 (by field_simp))
                (add safe 4 (by push_neg))
                (add unsafe 100% (by nlinarith))
                (add unsafe 100% (by simp_all))
                (add unsafe 90% (by field_simp [*] at *))
                (add unsafe 90% (by norm_num [*] at *))
                (add unsafe 80% (by gcongr))
                (add unsafe 80% (by linarith))
                (add unsafe 70% (by bound))
                (add unsafe 70% (by norm_cast at *))
                (add unsafe 70% (by omega))
                (add unsafe 70% (by positivity))
                (add unsafe 70% (by ring_nf at *))
                (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
                (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

              have h9 : 3 * (m : ℝ) - 1 ≤ (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1 := by
                clear * - h8
                aesop (config := {
                maxNormIterations       := 120
                })
                (add safe 4 (by field_simp))
                (add safe 4 (by push_neg))
                (add unsafe 100% (by nlinarith))
                (add unsafe 100% (by simp_all))
                (add unsafe 90% (by field_simp [*] at *))
                (add unsafe 90% (by norm_num [*] at *))
                (add unsafe 80% (by gcongr))
                (add unsafe 80% (by linarith))
                (add unsafe 70% (by bound))
                (add unsafe 70% (by norm_cast at *))
                (add unsafe 70% (by omega))
                (add unsafe 70% (by positivity))
                (add unsafe 70% (by ring_nf at *))
                (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
                (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

              have h10 : (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1 = ((m + 1) : ℝ) ^ 2 := by
                clear * -
                aesop (config := {
                maxNormIterations       := 120
                })
                (add safe 4 (by field_simp))
                (add safe 4 (by push_neg))
                (add unsafe 100% (by nlinarith))
                (add unsafe 100% (by simp_all))
                (add unsafe 90% (by field_simp [*] at *))
                (add unsafe 90% (by norm_num [*] at *))
                (add unsafe 80% (by gcongr))
                (add unsafe 80% (by linarith))
                (add unsafe 70% (by bound))
                (add unsafe 70% (by norm_cast at *))
                (add unsafe 70% (by omega))
                (add unsafe 70% (by positivity))
                (add unsafe 70% (by ring_nf at *))
                (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
                (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

              clear * - h9 h10
              aesop (config := {
              maxNormIterations       := 120
              })
              (add safe 4 (by field_simp))
              (add safe 4 (by push_neg))
              (add unsafe 100% (by nlinarith))
              (add unsafe 100% (by simp_all))
              (add unsafe 90% (by field_simp [*] at *))
              (add unsafe 90% (by norm_num [*] at *))
              (add unsafe 80% (by gcongr))
              (add unsafe 80% (by linarith))
              (add unsafe 70% (by bound))
              (add unsafe 70% (by norm_cast at *))
              (add unsafe 70% (by omega))
              (add unsafe 70% (by positivity))
              (add unsafe 70% (by ring_nf at *))
              (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
              (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
              (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

            clear * - h5 hm
            simp_all only [succ_eq_add_one, zero_add, le_eq, tsub_le_iff_right, one_div, mul_inv_rev, ge_iff_le]
            rw [div_le_iff] <;> field_simp
            rw [le_div_iff]
            · nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ (m : ℝ))]
            · positivity

          clear * - h2 h3 h4
          aesop (config := {
          maxNormIterations       := 120
          })
          (add safe 4 (by field_simp))
          (add safe 4 (by push_neg))
          (add unsafe 100% (by nlinarith))
          (add unsafe 100% (by simp_all))
          (add unsafe 90% (by field_simp [*] at *))
          (add unsafe 90% (by norm_num [*] at *))
          (add unsafe 80% (by gcongr))
          (add unsafe 80% (by linarith))
          (add unsafe 70% (by bound))
          (add unsafe 70% (by norm_cast at *))
          (add unsafe 70% (by omega))
          (add unsafe 70% (by positivity))
          (add unsafe 70% (by ring_nf at *))
          (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
          (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
          (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

        clear * - h1
        simp_all only [one_div, mul_inv_rev, tsub_le_iff_right, ge_iff_le]
        linarith

      have h_quadratic : (m : ℝ) ^ 2 - (m : ℝ) + 2 ≥ 0 := by
        have h1 : (m : ℝ) ^ 2 - (m : ℝ) + 2 = ((m : ℝ) - 1/2 : ℝ) ^ 2 + 7/4 := by
          clear * -
          aesop (config := {
          maxNormIterations       := 120
          })
          (add safe 4 (by field_simp))
          (add safe 4 (by push_neg))
          (add unsafe 100% (by nlinarith))
          (add unsafe 100% (by simp_all))
          (add unsafe 90% (by field_simp [*] at *))
          (add unsafe 90% (by norm_num [*] at *))
          (add unsafe 80% (by gcongr))
          (add unsafe 80% (by linarith))
          (add unsafe 70% (by bound))
          (add unsafe 70% (by norm_cast at *))
          (add unsafe 70% (by omega))
          (add unsafe 70% (by positivity))
          (add unsafe 70% (by ring_nf at *))
          (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
          (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

        have h2 : ((m : ℝ) - 1/2 : ℝ) ^ 2 + 7/4 ≥ 0 := by
          clear * -
          aesop (config := {
          maxNormIterations       := 120
          })
          (add safe 4 (by field_simp))
          (add safe 4 (by push_neg))
          (add unsafe 100% (by nlinarith))
          (add unsafe 100% (by simp_all))
          (add unsafe 90% (by field_simp [*] at *))
          (add unsafe 90% (by norm_num [*] at *))
          (add unsafe 80% (by gcongr))
          (add unsafe 80% (by linarith))
          (add unsafe 70% (by bound))
          (add unsafe 70% (by norm_cast at *))
          (add unsafe 70% (by omega))
          (add unsafe 70% (by positivity))
          (add unsafe 70% (by ring_nf at *))
          (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
          (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

        clear * - h1 h2
        aesop (config := {
        maxNormIterations       := 120
        })
        (add safe 4 (by field_simp))
        (add safe 4 (by push_neg))
        (add unsafe 100% (by nlinarith))
        (add unsafe 100% (by simp_all))
        (add unsafe 90% (by field_simp [*] at *))
        (add unsafe 90% (by norm_num [*] at *))
        (add unsafe 80% (by gcongr))
        (add unsafe 80% (by linarith))
        (add unsafe 70% (by bound))
        (add unsafe 70% (by norm_cast at *))
        (add unsafe 70% (by omega))
        (add unsafe 70% (by positivity))
        (add unsafe 70% (by ring_nf at *))
        (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
        (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

      have h_final : P (m + 1) ≤ B (m + 1) := by
        have h1 : P (m + 1) ≤ B m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) := h_step1
        have h2 : B m * (1 + (1 : ℝ) / ((m + 1) : ℝ) ^ 3) ≤ B (m + 1) := by
          aesop (config := {
          maxNormIterations       := 120
          })
          (add safe 4 (by field_simp))
          (add safe 4 (by push_neg))
          (add unsafe 100% (by nlinarith))
          (add unsafe 100% (by simp_all))
          (add unsafe 90% (by field_simp [*] at *))
          (add unsafe 90% (by norm_num [*] at *))
          (add unsafe 80% (by gcongr))
          (add unsafe 80% (by linarith))
          (add unsafe 70% (by bound))
          (add unsafe 70% (by norm_cast at *))
          (add unsafe 70% (by omega))
          (add unsafe 70% (by positivity))
          (add unsafe 70% (by ring_nf at *))
          (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
          (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
          (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

        clear * - h1 h2
        simp_all only [one_div, Nat.cast_add, Nat.cast_one, ge_iff_le, P, B]
        linarith

      exact h_final

  have h_main : P n ≤ B n := h_induction n h₀
  exact h_main
