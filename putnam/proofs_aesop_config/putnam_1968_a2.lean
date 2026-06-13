
import Mathlib

set_option maxHeartbeats 0

theorem putnam_1968_a2
(a b c d e f : ℤ)
(ε : ℝ)
(hne : a * d ≠ b * c)
(hε : ε > 0)
: ∃ r s : ℚ, (|r * a + s * b - e| : ℝ) ∈ Set.Ioo 0 ε ∧ (|r * c + s * d - f| : ℝ) ∈ Set.Ioo 0 ε := by
  let D : ℚ := (a * d - b * c : ℚ)
  have hD_nonzero : D ≠ 0 := by
    clear * - hne
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have hδ₁_exists : ∃ δ₁ : ℚ, (δ₁ : ℝ) ∈ Set.Ioo 0 ε := by
    clear * - hε
    simp_all only [gt_iff_lt, Set.mem_Ioo, Rat.cast_pos]
    obtain ⟨δ₂, hδ₂, _⟩ := exists_rat_btwn hε
    simp_all only [Rat.cast_pos]
    have := exists_rat_btwn hδ₂
    simp_all only [Rat.cast_eq_id, id_eq]
    cases' this with δ₁ hδ₁
    use δ₁
    simp_all only [true_and]
    linarith [show (δ₁ : ℝ) < δ₂ by exact_mod_cast hδ₁.2]

  let δ₁ : ℚ := Classical.choose hδ₁_exists
  have hδ₁_in_Ioo : (δ₁ : ℝ) ∈ Set.Ioo 0 ε := by
    clear * - hδ₁_exists
    simp_all [δ₁]
    cases Classical.choose_spec hδ₁_exists
    simp_all only [Set.mem_Ioo, Rat.cast_pos, and_self]

  have hδ₁_pos : 0 < (δ₁ : ℝ) := by
    clear * - hδ₁_in_Ioo
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

  have hδ₁_lt_eps : (δ₁ : ℝ) < ε := by
    clear * - hδ₁_in_Ioo
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

  have hδ₂_exists : ∃ δ₂ : ℚ, (δ₂ : ℝ) ∈ Set.Ioo 0 ε := by
    clear * - hε
    simp_all only [gt_iff_lt, Set.mem_Ioo, Rat.cast_pos]
    simpa using exists_rat_btwn hε

  let δ₂ : ℚ := Classical.choose hδ₂_exists
  have hδ₂_in_Ioo : (δ₂ : ℝ) ∈ Set.Ioo 0 ε := by
    clear * - hδ₂_exists
    simp_all [δ₂]
    simpa using Classical.choose_spec hδ₂_exists

  have hδ₂_pos : 0 < (δ₂ : ℝ) := by
    clear * - hδ₂_in_Ioo
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

  have hδ₂_lt_eps : (δ₂ : ℝ) < ε := by
    clear * - hδ₂_in_Ioo
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

  let u : ℚ := (e : ℚ) + δ₁
  let v : ℚ := (f : ℚ) + δ₂
  let r : ℚ := ((d : ℚ) * u - (b : ℚ) * v) / D
  let s : ℚ := ((a : ℚ) * v - (c : ℚ) * u) / D
  have h_r_in_Q : True := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    useSimpAll              := false
    })
    (add safe 3 (by norm_cast))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by norm_cast at *))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 10% (by first | apply eq_self_iff_true | rw [eq_self_iff_true] | simp only [eq_self_iff_true]))
    (add unsafe 10% (by first | apply forall_eq | rw [forall_eq] | simp only [forall_eq]))
    (add unsafe 10% (by first | apply forall_true_iff | rw [forall_true_iff] | simp only [forall_true_iff]))

  have h_s_in_Q : True := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    useSimpAll              := false
    })
    (add safe 3 (by norm_cast))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by norm_cast at *))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 10% (by first | apply eq_self_iff_true | rw [eq_self_iff_true] | simp only [eq_self_iff_true]))
    (add unsafe 10% (by first | apply forall_eq | rw [forall_eq] | simp only [forall_eq]))
    (add unsafe 10% (by first | apply forall_true_iff | rw [forall_true_iff] | simp only [forall_true_iff]))

  have h_num_expansion : ((d : ℚ) * u - (b : ℚ) * v) * (a : ℚ) + ((a : ℚ) * v - (c : ℚ) * u) * (b : ℚ) = (a * d - b * c : ℚ) * u := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_frac_simplifies : (((d : ℚ) * u - (b : ℚ) * v) * (a : ℚ) + ((a : ℚ) * v - (c : ℚ) * u) * (b : ℚ)) / D = u := by
    clear * - h_num_expansion hD_nonzero
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_ra_sb_eq_u : (r : ℚ) * (a : ℚ) + (s : ℚ) * (b : ℚ) = u := by
    clear * - h_frac_simplifies
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_num_expansion_cd : ((d : ℚ) * u - (b : ℚ) * v) * (c : ℚ) + ((a : ℚ) * v - (c : ℚ) * u) * (d : ℚ) = (a * d - b * c : ℚ) * v := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_frac_simplifies_cd : (((d : ℚ) * u - (b : ℚ) * v) * (c : ℚ) + ((a : ℚ) * v - (c : ℚ) * u) * (d : ℚ)) / D = v := by
    clear * - h_num_expansion_cd hD_nonzero
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_rc_sd_eq_v : (r : ℚ) * (c : ℚ) + (s : ℚ) * (d : ℚ) = v := by
    clear * - h_frac_simplifies_cd
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_abs1_eq_u : |(r : ℝ) * (a : ℝ) + (s : ℝ) * (b : ℝ) - (e : ℝ)| = |(u : ℝ) - (e : ℝ)| := by
    clear * - h_ra_sb_eq_u
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

  have h_abs1_eq_d1 : |(u : ℝ) - (e : ℝ)| = (δ₁ : ℝ) := by
    clear * -
    simp_all [u, δ₁]
    by_contra H
    simp_all only [not_le]
    norm_cast at *
    have hu_pos : 0 < u
    · simp_all [u, δ₁]
      exfalso
      have := Classical.choose_spec hδ₁_exists
      simp_all
      linarith
    · simp_all [u, δ₁]
      have := Classical.choose_spec hδ₁_exists
      simp_all
      linarith [this.1]

  have h_abs2_eq_v : |(r : ℝ) * (c : ℝ) + (s : ℝ) * (d : ℝ) - (f : ℝ)| = |(v : ℝ) - (f : ℝ)| := by
    clear * - h_rc_sd_eq_v
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

  have h_abs2_eq_d2 : |(v : ℝ) - (f : ℝ)| = (δ₂ : ℝ) := by
    clear * -
    simp_all [v, δ₂]
    have := Classical.choose_spec hδ₂_exists
    simp_all
    linarith

  have h_abs1_pos : 0 < |(r : ℝ) * (a : ℝ) + (s : ℝ) * (b : ℝ) - (e : ℝ)| := by
    clear * - h_abs1_eq_u h_abs1_eq_d1 hδ₁_pos
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

  have h_abs1_lt : |(r : ℝ) * (a : ℝ) + (s : ℝ) * (b : ℝ) - (e : ℝ)| < ε := by
    clear * - h_abs1_eq_u h_abs1_eq_d1 hδ₁_lt_eps
    simp_all [δ₁, r, u, v, δ₂, D, s]
    norm_cast
    simp_all only [Rat.cast_abs]
    norm_cast
    simp_all only [Rat.cast_abs]
    rwa [abs_of_nonneg]
    simp_all only [Rat.cast_nonneg]

  have h_abs1_in_Ioo : (|(r : ℝ) * (a : ℝ) + (s : ℝ) * (b : ℝ) - (e : ℝ)| : ℝ) ∈ Set.Ioo 0 ε := by
    clear * - h_abs1_pos h_abs1_lt
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

  have h_abs2_pos : 0 < |(r : ℝ) * (c : ℝ) + (s : ℝ) * (d : ℝ) - (f : ℝ)| := by
    clear * - h_abs2_eq_v h_abs2_eq_d2 hδ₂_pos
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

  have h_abs2_lt : |(r : ℝ) * (c : ℝ) + (s : ℝ) * (d : ℝ) - (f : ℝ)| < ε := by
    clear * - h_abs2_eq_v h_abs2_eq_d2 hδ₂_lt_eps
    simp_all [δ₂, r, u, δ₁, v, D, s]
    norm_cast
    simp_all only [Rat.cast_abs]
    norm_cast
    simp_all only [Rat.cast_abs]
    norm_cast
    simp_all only [Rat.cast_abs]
    norm_cast
    simp_all only [Rat.cast_abs]
    norm_cast at *
    simp_all only [Int.cast_sub, Int.cast_mul, Rat.cast_abs]
    rw [abs_of_nonneg]
    · simp_all only
    · simp_all only [Rat.cast_nonneg]

  have h_abs2_in_Ioo : (|(r : ℝ) * (c : ℝ) + (s : ℝ) * (d : ℝ) - (f : ℝ)| : ℝ) ∈ Set.Ioo 0 ε := by
    clear * - h_abs2_pos h_abs2_lt
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

  have h_final : ∃ r' s' : ℚ, (|(r' : ℝ) * (a : ℝ) + (s' : ℝ) * (b : ℝ) - (e : ℝ)| : ℝ) ∈ Set.Ioo 0 ε ∧ (|(r' : ℝ) * (c : ℝ) + (s' : ℝ) * (d : ℝ) - (f : ℝ)| : ℝ) ∈ Set.Ioo 0 ε := by
    clear * - h_abs1_in_Ioo h_abs2_in_Ioo
    simp_all [r, u, δ₁, v, δ₂, D, s]
    use r, s
    simp_all only [Set.mem_Ioo, Rat.cast_pos, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast, Rat.cast_add,
      not_false_eq_true, and_self, r, u, δ₁, v, δ₂, D, s]

  exact h_final
