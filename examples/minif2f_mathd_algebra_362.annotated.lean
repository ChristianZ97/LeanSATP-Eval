/-
================================================================================
  ANNOTATED SUCCESS PROOF — MiniF2F-test :: mathd_algebra_362
================================================================================
  Problem.  Given  a^2 * b^3 = 32/27  and  a / b^3 = 27/4,  prove  a + b = 8/3.

  This is the DSP cascade output (mode `satpbfsaesop4x`, ckpt 5f5167ad, run
  20260602_040745), made service-free: it compiles with `import Mathlib` alone,
  no SATP/BFS server. Byte-identical to proofs_aesop_config/mathd_algebra_362.lean.

  Gap attribution (layer_histogram = {satp: 4, bfs_1: 4}).  Each `have` below is
  ONE decomposed gap of the sketch; the tag says which solver in the cost-tiered
  cascade closed it:

    [satp]   closed by the 0.2B SATP policy — emitted as a deterministic
             `aesop (config := {...}) (add safe/unsafe ...)` ruleset. One argmax
             call, no 27B search budget consumed.
    [BFS-1]  closed by BFS-Prover-V2-7B on retry attempt 1 (the `_1` in `bfs_1`).
             These are the gaps needing genuine case analysis / root extraction.

  The split is the paper's thesis in miniature: SATP cheaply discharges the
  routine rearrange/substitute/evaluate gaps; BFS is spent only on the few gaps
  that require a case-split + nlinarith certificate.
-/

import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_362 (a b : ℝ) (h₀ : a ^ 2 * b ^ 3 = 32 / 27) (h₁ : a / b ^ 3 = 27 / 4) :
    a + b = 8 / 3 := by
  -- [satp]   h2:  Multiply the two hypotheses: a^2 b^3 * (a / b^3) = (32/27)(27/4).
  have h2 : a ^ 2 * b ^ 3 * (a / b ^ 3) = (32 / 27) * (27 / 4) := by
    clear * - h₀ h₁
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

  -- [BFS-1]  h3:  Reduce to a^3 = 8 (case-split b = 0 vs b ≠ 0, then field_simp + nlinarith).
  have h3 : a ^ 3 = 8 := by
    clear * - h2
    rcases eq_or_ne b 0 with (rfl | hb)
    ·
      simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero, zero_eq_mul,
        div_eq_zero_iff, or_self]
    · simp_all only [ne_eq]
      field_simp at * <;> ring
      apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 3 hb)) <;> nlinarith

  -- [BFS-1]  h4:  Extract the real cube root: a^3 = 8  ⟹  a = 2.
  have h4 : a = (2 : ℝ) := by
    clear * - h3
    nlinarith [sq_nonneg (a ^ 2)]

  -- [satp]   h5:  Back-substitute a = 2 into a / b^3 = 27/4, giving 2 / b^3 = 27/4.
  have h5 : (2 : ℝ) / b ^ 3 = 27 / 4 := by
    clear * - h4 h₁
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

  -- [BFS-1]  h6:  Solve for b^3 = 8/27.
  have h6 : b ^ 3 = 8 / 27 := by
    clear * - h5
    rcases eq_or_ne b 0 with (rfl | hb) <;> field_simp at * <;> linarith

  -- [BFS-1]  h7:  Extract the cube root: b = 2/3.
  have h7 : b = (2 : ℝ) / 3 := by
    clear * - h6
    nlinarith [sq_nonneg (b ^ 2 - 4 / 9)]

  -- [satp]   h8:  Assemble a + b = 2 + 2/3.
  have h8 : a + b = (2 : ℝ) + (2 : ℝ) / 3 := by
    clear * - h4 h7
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
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

  -- [satp]   h9:  Normalise  2 + 2/3 = 8/3.
  have h9 : a + b = 8 / 3 := by
    clear * - h8
    aesop (config := {
    maxNormIterations       := 120
    })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
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

  exact h9
