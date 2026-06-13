
import Mathlib
open Matrix Function Real

set_option maxHeartbeats 0

theorem putnam_2012_b1
(S : Set (Set.Ici (0 : ℝ) → ℝ))
(rngS : ∀ f ∈ S, ∀ x : Set.Ici (0 : ℝ), f x ∈ Set.Ici (0 : ℝ))
(f1 : Set.Ici (0 : ℝ) → ℝ)
(hf1 : f1 = fun (x : Set.Ici (0 : ℝ)) ↦ exp x - 1)
(f2 : Set.Ici (0 : ℝ) → ℝ)
(hf2 : f2 = fun (x : Set.Ici (0 : ℝ)) ↦ Real.log (x + 1))
(hf1mem : f1 ∈ S)
(hf2mem : f2 ∈ S)
(hsum : ∀ f ∈ S, ∀ g ∈ S, (fun x ↦ (f x) + (g x)) ∈ S)
(hcomp : ∀ f ∈ S, ∀ g ∈ S, ∀ gnneg : Set.Ici (0 : ℝ) → Set.Ici (0 : ℝ), ((∀ x : Set.Ici (0 : ℝ), g x = gnneg x) → (fun x ↦ f (gnneg x)) ∈ S))
(hdiff : ∀ f ∈ S, ∀ g ∈ S, (∀ x : Set.Ici (0 : ℝ), f x ≥ g x) → (fun x ↦ (f x) - (g x)) ∈ S)
: (∀ f ∈ S, ∀ g ∈ S, (fun x ↦ (f x) * (g x)) ∈ S) := by
  intro f hf g hg

  have h_f_nn : ∀ x, 0 ≤ f x := by
    clear * - rngS hf
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

  have h_g_nn : ∀ x, 0 ≤ g x := by
    clear * - rngS hg
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

  let gnneg_f : Set.Ici (0 : ℝ) → Set.Ici (0 : ℝ) := fun x ↦ ⟨f x, h_f_nn x⟩
  let comp_f2_f : Set.Ici (0 : ℝ) → ℝ := fun x ↦ f2 (gnneg_f x)

  have h_comp_f2_f_mem : comp_f2_f ∈ S := by
    clear * - hcomp hf2mem hf h_f_nn
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

  let gnneg_g : Set.Ici (0 : ℝ) → Set.Ici (0 : ℝ) := fun x ↦ ⟨g x, h_g_nn x⟩
  let comp_f2_g : Set.Ici (0 : ℝ) → ℝ := fun x ↦ f2 (gnneg_g x)

  have h_comp_f2_g_mem : comp_f2_g ∈ S := by
    clear * - hcomp hf2mem hg h_g_nn
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

  let sum_comps : Set.Ici (0 : ℝ) → ℝ := fun x ↦ comp_f2_f x + comp_f2_g x

  have h_sum_comps_mem : sum_comps ∈ S := by
    clear * - hsum h_comp_f2_f_mem h_comp_f2_g_mem
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

  have h_sum_comps_nn : ∀ x, 0 ≤ sum_comps x := by
    clear * - rngS h_sum_comps_mem
    simp_all [sum_comps, comp_f2_f, gnneg_f, comp_f2_g, gnneg_g]
    intro a h_nonneg_a
    have h1 := h_sum_comps_mem
    simp_all only [ge_iff_le]
    exact rngS _ h1 a h_nonneg_a

  let gnneg_sum : Set.Ici (0 : ℝ) → Set.Ici (0 : ℝ) := fun x ↦ ⟨sum_comps x, h_sum_comps_nn x⟩
  let comp_f1_sum : Set.Ici (0 : ℝ) → ℝ := fun x ↦ f1 (gnneg_sum x)

  have h_comp_f1_sum_mem : comp_f1_sum ∈ S := by
    clear * - hcomp hf1mem h_sum_comps_mem h_sum_comps_nn
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

  let sum_fg : Set.Ici (0 : ℝ) → ℝ := fun x ↦ f x + g x

  have h_sum_fg_mem : sum_fg ∈ S := by
    clear * - hsum hf hg
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

  have h_ineq : ∀ x, comp_f1_sum x ≥ sum_fg x := by
    clear * - hf1 hf2 h_f_nn h_g_nn comp_f1_sum sum_fg sum_comps
    simp_all [comp_f1_sum, gnneg_sum, sum_comps, comp_f2_f, gnneg_f, comp_f2_g, gnneg_g, sum_fg]
    intro a ha
    rw [exp_add, exp_log, exp_log] <;> aesop
    · rw [mul_comm]
      nlinarith [h_f_nn ⟨a, ha⟩, h_g_nn ⟨a, ha⟩]
    · linarith [h_g_nn ⟨a, ha⟩]
    · linarith [h_f_nn ⟨a, ha⟩]

  let diff_func : Set.Ici (0 : ℝ) → ℝ := fun x ↦ comp_f1_sum x - sum_fg x

  have h_diff_mem : diff_func ∈ S := by
    clear * - hdiff h_comp_f1_sum_mem h_sum_fg_mem h_ineq
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

  have h_diff_is_prod : ∀ x, diff_func x = f x * g x := by
    clear * - hf1 hf2 h_f_nn h_g_nn diff_func sum_fg comp_f1_sum
    simp_all [diff_func, comp_f1_sum, gnneg_sum, sum_comps, comp_f2_f, gnneg_f, comp_f2_g, gnneg_g, sum_fg]
    intro a ha
    rw [exp_add, exp_log, exp_log] <;> aesop
    · ring
    · linarith [h_g_nn ⟨a, ha⟩]
    · linarith [h_f_nn ⟨a, ha⟩]

  have h_prod_mem : (fun x ↦ f x * g x) ∈ S := by
    clear * - h_diff_mem h_diff_is_prod
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

  exact h_prod_mem
