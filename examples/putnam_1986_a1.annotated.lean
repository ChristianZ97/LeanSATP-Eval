/-
================================================================================
  ANNOTATED SUCCESS PROOF — PutnamBench :: putnam_1986_a1
================================================================================
  Problem.  Let S = { x : R | x^4 + 36 <= 13 x^2 }  and  f x = x^3 - 3x.
            Show  IsGreatest { f x | x in S }  18.

  DSP cascade output (mode `satpbfsaesop4x`, ckpt 5f5167ad), made service-free:
  compiles with `import Mathlib` alone, no SATP/BFS server.

  Gap attribution (layer_histogram = {satp: 11, bfs_1: 3}).  Tags as above:

    [satp]   0.2B SATP policy, one deterministic `aesop (config := {...})` call
             (full ruleset shown once; identical block thereafter).
    [BFS-1]  BFS-Prover-V2-7B, retry attempt 1.

  Complementarity at Putnam difficulty: the 11 routine gaps (unfold f, compute
  the derivative, evaluate f at the endpoints, locate critical points) are all
  SATP; BFS is reserved for exactly the 3 structurally hard gaps —
    h1   characterise S as the union of two intervals [-3,-2] u [2,3],
    h13  the global upper bound  forall x in S, f x <= 18,
    h14  assembling `IsGreatest` from attainment + upper bound.
-/


import Mathlib

set_option maxHeartbeats 0

abbrev putnam_1986_a1_solution : ℝ := 18
theorem putnam_1986_a1
    (S : Set ℝ) (f : ℝ → ℝ)
    (hS : S = {x : ℝ | x ^ 4 + 36 ≤ 13 * x ^ 2})
    (hf : f = fun x ↦ x ^ 3 - 3 * x) :
    IsGreatest
    {f x | x ∈ S}
    putnam_1986_a1_solution := by
  -- [BFS-1]  h1:  Characterise the constraint set: S = [-3,-2] u [2,3] (case-split on sign of a, nlinarith).
  have h1 : S = Set.Icc (-3) (-2) ∪ Set.Icc (2 : ℝ) 3 := by
    clear * - hS
    simp_all only
    ext a <;> norm_num
    aesop (add simp [or_comm])
    · obtain h | h := le_total a 0
      · right
        constructor <;> nlinarith [sq_nonneg (a ^ 2 - 4), sq_nonneg (a ^ 2 - 9)]
      ·
        exact
          Or.inl
            ⟨by nlinarith [sq_nonneg (a ^ 2 - 4), sq_nonneg (a ^ 2 - 9)], by
              nlinarith [sq_nonneg (a ^ 2 - 4), sq_nonneg (a ^ 2 - 9)]⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr left) (sub_nonneg.mpr right), sq_nonneg (a ^ 2 - 5)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr right) (sub_nonneg.mpr left), sq_nonneg (a ^ 2 - 5)]

  -- [satp]  h2:  Unfold  f x = x^3 - 3x.
  have h2 : ∀ x : ℝ, f x = x ^ 3 - 3 * x := by
    clear * - hf
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

  -- [satp]  h3:  Compute  deriv f x = 3 x^2 - 3.
  have h3 : ∀ x : ℝ, deriv f x = 3 * x ^ 2 - 3 := by
    clear * - hf
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

  -- [satp]  h4:  Critical points:  deriv f (1) = 0  and  deriv f (-1) = 0.
  have h4 : deriv f 1 = 0 ∧ deriv f (-1) = 0 := by
    clear * - h3
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

  -- [satp]  h5:  The critical points +/-1 lie OUTSIDE S.
  have h5 : (1 : ℝ) ∉ S ∧ (-1 : ℝ) ∉ S := by
    clear * - h1 h4
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

  -- [satp]  h6:  Evaluate  f(-3) = -18.
  have h6 : f (-3) = -18 := by
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

  -- [satp]  h7:  Evaluate  f(-2) = -2.
  have h7 : f (-2) = -2 := by
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

  -- [satp]  h8:  Evaluate  f(2) = 2.
  have h8 : f 2 = 2 := by
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

  -- [satp]  h9:  Evaluate  f(3) = 18.
  have h9 : f 3 = 18 := by
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

  -- [satp]  h10:  f(3) equals the claimed maximum 18.
  have h10 : f 3 = putnam_1986_a1_solution := by
    clear * - h9
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

  -- [satp]  h11:  Endpoint membership:  3 in S.
  have h11 : 3 ∈ S := by
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
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  -- [satp]  h12:  The value 18 is ATTAINED:  18 in { f x | x in S }.
  have h12 : (putnam_1986_a1_solution : ℝ) ∈ {f x | x ∈ S} := by
    clear * - h10 h11
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
    (add unsafe 30% (by first | apply Ideal.quotientToQuotientRangePowQuotSucc_mk | rw [Ideal.quotientToQuotientRangePowQuotSucc_mk] | simp only [Ideal.quotientToQuotientRangePowQuotSucc_mk]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  -- [BFS-1]  h13:  Global UPPER BOUND:  forall x in S, f x <= 18  (interval case-split + nlinarith).
  have h13 : ∀ x ∈ S, f x ≤ putnam_1986_a1_solution := by
    clear * - h1 h2 h3 h5
    simp_all
    norm_num [putnam_1986_a1_solution]
    rintro x (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]

  -- [BFS-1]  h14:  Assemble IsGreatest from attainment (h12) and upper bound (h13).
  have h14 : IsGreatest {f x | x ∈ S} putnam_1986_a1_solution := by
    clear * - h12 h13
    simp_all only [Set.mem_setOf_eq]
    constructor
    · simp_all only [Set.mem_setOf_eq]
    · rintro y ⟨z, hz1, hz2⟩
      simp only [← hz2, h13 z hz1]

  exact h14
