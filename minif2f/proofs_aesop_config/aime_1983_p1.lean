import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have h_s1 : Real.log w / Real.log x = (24 : ℝ) := by
    clear * - h0
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

  have h_s2 : Real.log x = Real.log w / (24 : ℝ) := by
    clear * - h_s1
    rw [div_eq_iff] at * <;> aesop

  have h_s3 : Real.log w / Real.log y = (40 : ℝ) := by
    clear * - h1
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

  have h_s4 : Real.log y = Real.log w / (40 : ℝ) := by
    clear * - h_s3
    rw [← inv_inj] <;> field_simp
    simp_all only [one_div]
    rcases eq_or_ne (Real.log y) 0 with h | h
    · simp_all only [div_zero, OfNat.zero_ne_ofNat]
    · simp_all only [ne_eq, log_eq_zero, Nat.cast_eq_zero, cast_eq_one, not_or]
      rcases eq_or_ne (Real.log y) 0 with h0 | h0 <;> field_simp [h0] at * <;> aesop

  have h_s5 : Real.log w / Real.log (x * y * z) = (12 : ℝ) := by
    clear * - h2
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

  have h_s6 : Real.log (x * y * z) = Real.log w / (12 : ℝ) := by
    clear * - h_s5
    have : Real.log (x * y * z : ℝ) ≠ 0
    · simp_all only [ne_eq, log_eq_zero, _root_.mul_eq_zero, Nat.cast_eq_zero, not_or]
      apply And.intro <;> aesop
    · simp_all only [ne_eq, log_eq_zero, _root_.mul_eq_zero, Nat.cast_eq_zero, not_or]
      field_simp [← h_s5]
      rw [div_eq_iff] at h_s5 <;> aesop

  have h_s7 : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
    clear * - ht
    rw [Real.log_mul]
    · simp_all only [add_left_inj]
      exact Real.log_mul (by aesop) (by aesop)
    · simp_all only [ne_eq, _root_.mul_eq_zero, Nat.cast_eq_zero, not_or]
      repeat' omega
    · simp_all only [ne_eq, Nat.cast_eq_zero]
      omega

  have h_s8 : Real.log w / (24 : ℝ) + Real.log w / (40 : ℝ) + Real.log z = Real.log w / (12 : ℝ) := by
    clear * - h_s2 h_s4 h_s6 h_s7
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
    (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_s9 : (1 : ℝ) / 24 + (1 : ℝ) / 40 + Real.log z / Real.log w = (1 : ℝ) / 12 := by
    clear * - h_s8 ht h0
    simp_all only [one_div]
    obtain ⟨hx, _, _⟩ := ht
    field_simp [← eq_sub_iff_add_eq] at *
    rcases eq_or_ne (Real.log w) 0 with hw | hw <;> field_simp [hw] at * <;> linarith

  have h_s10 : (1 : ℝ) / 24 + (1 : ℝ) / 40 = (1 : ℝ) / 15 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    useSimpAll              := false
    })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 40% (by first | apply Int.negOnePow_zero | rw [Int.negOnePow_zero] | simp only [Int.negOnePow_zero]))
    (add unsafe 30% (by first | apply TrivSqZeroExt.fst_add | rw [TrivSqZeroExt.fst_add] | simp only [TrivSqZeroExt.fst_add]))

  have h_s11 : (1 : ℝ) / 15 + Real.log z / Real.log w = (1 : ℝ) / 12 := by
    clear * - h_s9 h_s10
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

  have h_s12 : Real.log z / Real.log w = (1 : ℝ) / 12 - (1 : ℝ) / 15 := by
    clear * - h_s11
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

  have h_s13 : (1 : ℝ) / 12 - (1 : ℝ) / 15 = (1 : ℝ) / 60 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    useSimpAll              := false
    })
    (add safe 1 (by field_simp))
    (add safe 1 (by ring))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 40% (by first | apply sub_half | rw [sub_half] | simp only [sub_half]))
    (add unsafe 30% (by first | apply div_sub' | rw [div_sub'] | simp only [div_sub']))
    (add unsafe 30% (by first | apply one_div | rw [one_div] | simp only [one_div]))
    (add unsafe 10% (by first | apply Real.sqrt_div_self' | rw [Real.sqrt_div_self'] | simp only [Real.sqrt_div_self']))
    (add unsafe 10% (by first | apply mul_one_div | rw [mul_one_div] | simp only [mul_one_div]))
    (add unsafe 10% (by first | apply one_sub_div | rw [one_sub_div] | simp only [one_sub_div]))
    (add unsafe 10% (by first | apply sub_div | rw [sub_div] | simp only [sub_div]))

  have h_s14 : Real.log z / Real.log w = (1 : ℝ) / 60 := by
    clear * - h_s12 h_s13
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

  have h_s15 : Real.log w / Real.log z = (60 : ℝ) := by
    clear * - h_s14
    simp_all only [one_div]
    have hx := h_s14
    simp_all only
    have _ := hx
    simp_all only
    apply inv_injective
    simp_all only [inv_div]

  exact h_s15
