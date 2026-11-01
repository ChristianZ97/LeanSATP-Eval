import Sec2.Growth
import Sec2.DSP.SelfBound

set_option maxHeartbeats 0

open Finset

namespace Sec2.DSP

variable {H M : ℕ}

/-- Lemma 2.4: for all `0 < α ≤ α₀ = 1 / ((4H + 1) Δ_r)` and all `l`,
`l' = l + α ∇_l J_sparse(l)` satisfies `0 ≤ p_s(l') − p_s(l) ≤ c · p_s(l)²` with
`c = 2 α H M Δ_r`. -/
theorem growth (hM : 0 < M) (Astar : Finset (Arm H M)) (rs rf : ℝ) (hr : rf < rs) :
    ∀ α : ℝ, 0 < α → α ≤ 1 / ((4 * H + 1) * (rs - rf)) → ∀ l : Logits H M,
      0 ≤ provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ∧
      provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ≤
        2 * α * ((H : ℝ) * M) * (rs - rf) * provingProb Astar l ^ 2 := by
  intro α hα hαle l
  -- [cite: gradient_expectedReward] the Setup's ∇_l J_sparse = Δ_r ∇_l p_s at l_k; it turns α ∇_l J_sparse(l_k) into δ
  have hS2 := gradient_expectedReward hM Astar rs rf l
  -- l.112 (definitions, not steps): write ∇_l p_k for ∇_l p_s(l_k), and δ = α Δ_r ∇_l p_k
  set g := gradient (provingProb Astar) l with hg
  set δ := (α * (rs - rf)) • g with hδ
  -- the chain (2.3)
  have h23 : provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l =
      provingProb Astar (l + δ) - provingProb Astar l :=
    calc provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l
        = provingProb Astar (l + α • gradient (expectedReward Astar rs rf) l) -
            provingProb Astar l := by
          -- [L24.1] p_{k+1} − p_k = p_s(l_k + α ∇_l J_sparse(l_k)) − p_s(l_k)
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * -
          aesop (config := {
              maxRuleApplications := 1600
              maxNormIterations := 320
              enableSimp := false
            })
              (add norm 100 (by norm_cast))
              (add norm 0 (by linarith))
              (add norm 0 (by nlinarith))
              (add norm 0 (by omega))
              (add norm 1 (by push_neg))
              (add norm 100 (by gcongr))
              (add norm 0 (by bound))
              (add norm 0 (by ring_nf))
              (add norm 1 (by ext))
              (add norm 1 (by simp))
              (add norm 1 (by field_simp [*] at *))
              (add safe 100 (by ring))
              (add safe 100 (by field_simp))
              (add safe 100 (by norm_num))
              (add safe 0 (by positivity))
              (add safe 100 (by interval_cases))
              (add safe 0 (by split))
              (add safe 0 (by norm_num [*] at *))
              (add safe 100 (by rfl))
              (add safe 100 (by decide))
              (add safe 0 (by push_cast))
              (add safe 100 (by assumption_mod_cast))
              (add norm 0 (by grind only [WeakFEPair.Λ₀_eq]))
              (add norm 0 (by grind only [mul_div_cancel_right]))
              (add norm 0 (by grind only [mul_div_cancel_left]))
              (add norm 0 (by grind only [skewAdjointPart]))
              (add norm 0 (by grind only [mul_div_cancel]))
              (add norm 0 (by grind only [aux_sub]))
              (add norm 0 (by grind only [QuadraticForm.map_add_self]))
              (add norm 0 (by grind only [mul_div_mul_comm]))
              (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux7]))
              (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux8]))
              (add norm 0 (by grind only [midpoint_add_sub]))
              (add norm 0 (by grind only [CliffordAlgebra.ι_mul_ι_mul_invOf_ι]))
              (add norm 0 (by grind only [star_sub]))
              (add norm 0 (by grind only [add_smul]))
              (add norm 0 (by grind only [smul_add]))
              (add norm 0 (by grind only [CliffordAlgebra.ι_mul_ι_mul_ι]))
              (add norm 0 (by grind only [sub_smul]))
              (add norm 0 (by grind only [WeakFEPair.Λ]))
              (add norm 0 (by grind only [realPart_apply_coe]))
              (add norm 0 (by grind only [CliffordAlgebra.ι_mul_ι_add_swap]))
              (add norm 0 (by grind only [tsirelson_inequality]))
              (add norm 0 (by grind only [imaginaryPart_apply_coe]))
              (add norm 0 (by grind only [AddCommGroup.modEq_sub_iff_add_modEq]))
              (add norm 0 (by grind only [realPart_add_I_smul_imaginaryPart]))
              (add norm 0 (by grind only [aux_add]))
              (add norm 0 (by grind only [smul_sub]))
              (add norm 0 (by grind only [selfAdjointPart]))
              (add norm 0 (by grind only [half_add_self]))
              (add norm 0 (by grind only [CliffordAlgebra.ι_mul_ι_comm]))
              (add safe 0 (by simp only [div_mul] at *))
              (add safe 0 (by simp only [div_div] at *))
              (add safe 0 (by simp only [mul_div] at *))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   (bound)
      _ = provingProb Astar (l + δ) - provingProb Astar l := by
          -- [L24.2] = p_s(l_k + δ) − p_s(l_k)
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * - hS2 hδ
          rw [hS2, hδ, smul_smul]
  have hp2 : ContDiff ℝ 2 (provingProb Astar) := by
    -- [aux] p_s is C² in the logits: the Taylor expansion of (2.3)→(2.4) needs it (the thesis uses it silently)
    -- [non-satp] Configuration A inferred by satp's policy fails (`satp?` did not finish within 2400 s and was terminated).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hM
    have hc : ∀ i : Fin H × Fin M, ContDiff ℝ 2 (fun l : Logits H M => l i) := by
      intro i
      exact (EuclideanSpace.proj i : Logits H M →L[ℝ] ℝ).contDiff
    have hpos : ∀ (l : Logits H M) (h : Fin H), (∑ m' : Fin M, Real.exp (l (h, m'))) ≠ 0 := by
      intro l h
      have h0 : 0 < ∑ m' : Fin M, Real.exp (l (h, m')) :=
        Finset.sum_pos (fun m' _ => Real.exp_pos _) ⟨⟨0, hM⟩, Finset.mem_univ _⟩
      exact h0.ne'
    have hs : ∀ h : Fin H, ContDiff ℝ 2 (fun l : Logits H M => ∑ m' : Fin M, Real.exp (l (h, m'))) :=
      fun h => ContDiff.sum fun m' _ => (hc (h, m')).exp
    have hsm : ∀ (h : Fin H) (m : Fin M), ContDiff ℝ 2 (fun l : Logits H M => softmax l h m) := by
      intro h m
      show ContDiff ℝ 2 (fun l : Logits H M => Real.exp (l (h, m)) / ∑ m' : Fin M, Real.exp (l (h, m')))
      exact ((hc (h, m)).exp).div (hs h) (fun l => hpos l h)
    have hpol : ∀ A : Arm H M, ContDiff ℝ 2 (fun l : Logits H M => policy l A) := by
      intro A
      have key : ∀ t : Finset (Fin H),
          ContDiff ℝ 2 (fun l : Logits H M => ∏ h ∈ t, softmax l h (A h)) := by
        intro t
        exact contDiff_prod fun h _ => hsm h (A h)
      exact key Finset.univ
    show ContDiff ℝ 2 (fun l : Logits H M => ∑ A ∈ Astar, policy l A)
    exact ContDiff.sum fun A _ => hpol A
  -- [aux, cite: differentiable_provingProb] p_s is differentiable, so ∇_l p_k is its gradient at l_k (used by L24.3)
  have hdp : Differentiable ℝ (provingProb Astar) := differentiable_provingProb Astar
  obtain ⟨ξ, hξ, hL243⟩ : ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      provingProb Astar (l + δ) - provingProb Astar l =
        (provingProb Astar l + @inner ℝ _ _ g δ +
            1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • δ)) ξ) -
          provingProb Astar l := by
    -- [L24.3] = (p_k + ∇_l p_kᵀ δ + ½ δᵀ (∇²_l p_s(ξ)) δ) − p_k   (Taylor expansion, for some ξ between l_k and l_k + δ; the point is l_k + ξ δ, and δᵀ ∇²_l p_s δ there is the second derivative of s ↦ p_s(l_k + s δ) at ξ)
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hp2 hg hdp
    have hA : ∀ s : ℝ, HasDerivAt (fun s : ℝ => l + s • δ) δ s := by
      intro s
      exact (((hasDerivAt_id' s).smul_const δ).const_add l).congr_deriv (one_smul ℝ δ)
    have hD : ∀ s : ℝ, HasDerivAt (fun s : ℝ => provingProb Astar (l + s • δ))
        (fderiv ℝ (provingProb Astar) (l + s • δ) δ) s := by
      intro s
      exact (hdp (l + s • δ)).hasFDerivAt.comp_hasDerivAt s (hA s)
    have hd0 : deriv (fun s : ℝ => provingProb Astar (l + s • δ)) 0 = inner ℝ g δ := by
      rw [(hD 0).deriv, zero_smul, add_zero, hg]
      all_goals simp only [gradient, InnerProductSpace.toDual_symm_apply]
    have hdf : Differentiable ℝ (fderiv ℝ (provingProb Astar)) := by
      have hc1 : ContDiff ℝ 1 (fderiv ℝ (provingProb Astar)) := by
        exact hp2.fderiv_right one_add_one_eq_two.le
      first
      | exact hc1.differentiable le_rfl
      | exact hc1.differentiable one_ne_zero
    have hd1 : Differentiable ℝ (fun s : ℝ => provingProb Astar (l + s • δ)) :=
      fun s => (hD s).differentiableAt
    have hd2 : Differentiable ℝ (deriv fun s : ℝ => provingProb Astar (l + s • δ)) := by
      have hdeq : (deriv fun s : ℝ => provingProb Astar (l + s • δ)) =
          fun s => fderiv ℝ (provingProb Astar) (l + s • δ) δ :=
        funext fun s => (hD s).deriv
      rw [hdeq]
      exact fun s => ((hdf (l + s • δ)).comp s (hA s).differentiableAt).clm_apply (differentiableAt_const δ)
    have key : ∀ f : ℝ → ℝ, Differentiable ℝ f → Differentiable ℝ (deriv f) →
        ∃ ξ ∈ Set.Ioo (0:ℝ) 1, f 1 - f 0 = deriv f 0 + 1 / 2 * deriv (deriv f) ξ := by
      intro f h1 h2
      have hF : ∀ x : ℝ, HasDerivAt (fun s => f s - s * deriv f 0 - (f 1 - f 0 - deriv f 0) * (s * s))
          (deriv f x - deriv f 0 - (f 1 - f 0 - deriv f 0) * (2 * x)) x := by
        intro x
        have hsq : HasDerivAt (fun s : ℝ => s * s) (2 * x) x := by
          exact ((hasDerivAt_id' x).mul (hasDerivAt_id' x)).congr_deriv (by ring)
        exact ((h1 x).hasDerivAt.sub (hasDerivAt_mul_const (deriv f 0))).sub
          (hsq.const_mul (f 1 - f 0 - deriv f 0))
      have hFc : ContinuousOn (fun s => f s - s * deriv f 0 - (f 1 - f 0 - deriv f 0) * (s * s))
          (Set.Icc 0 1) := fun x _ => (hF x).continuousAt.continuousWithinAt
      have hF01 : f 0 - 0 * deriv f 0 - (f 1 - f 0 - deriv f 0) * (0 * 0) =
          f 1 - 1 * deriv f 0 - (f 1 - f 0 - deriv f 0) * (1 * 1) := by ring
      obtain ⟨c, hc, hc0⟩ : ∃ c ∈ Set.Ioo (0:ℝ) 1,
          deriv f c - deriv f 0 - (f 1 - f 0 - deriv f 0) * (2 * c) = 0 :=
        exists_hasDerivAt_eq_zero (by norm_num) hFc hF01 (fun x _ => hF x)
      have hG : ∀ x : ℝ, HasDerivAt (fun s => deriv f s - s * (2 * (f 1 - f 0 - deriv f 0)))
          (deriv (deriv f) x - 2 * (f 1 - f 0 - deriv f 0)) x := fun x =>
        (h2 x).hasDerivAt.sub (hasDerivAt_mul_const (2 * (f 1 - f 0 - deriv f 0)))
      have hGc : ContinuousOn (fun s => deriv f s - s * (2 * (f 1 - f 0 - deriv f 0)))
          (Set.Icc 0 c) := fun x _ => (hG x).continuousAt.continuousWithinAt
      have hG0c : deriv f 0 - 0 * (2 * (f 1 - f 0 - deriv f 0)) =
          deriv f c - c * (2 * (f 1 - f 0 - deriv f 0)) := by
        linear_combination (-1 : ℝ) * hc0
      obtain ⟨ξ, hξ, hξ0⟩ : ∃ ξ ∈ Set.Ioo (0:ℝ) c,
          deriv (deriv f) ξ - 2 * (f 1 - f 0 - deriv f 0) = 0 :=
        exists_hasDerivAt_eq_zero hc.1 hGc hG0c (fun x _ => hG x)
      exact ⟨ξ, ⟨hξ.1, hξ.2.trans hc.2⟩, by linarith⟩
    obtain ⟨ξ, hξ, hξeq⟩ := key (fun s : ℝ => provingProb Astar (l + s • δ)) hd1 hd2
    refine ⟨ξ, hξ, ?_⟩
    have hξeq' : provingProb Astar (l + (1:ℝ) • δ) - provingProb Astar (l + (0:ℝ) • δ) =
        deriv (fun s : ℝ => provingProb Astar (l + s • δ)) 0 +
          1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • δ)) ξ := hξeq
    have e1 : provingProb Astar (l + (1:ℝ) • δ) = provingProb Astar (l + δ) := by rw [one_smul]
    have e0 : provingProb Astar (l + (0:ℝ) • δ) = provingProb Astar l := by rw [zero_smul, add_zero]
    linarith [hξeq', e1, e0, hd0]
  -- the chain (2.3)–(2.5)
  have h25 : provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l =
      @inner ℝ _ _ g ((α * (rs - rf)) • g) +
        1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • ((α * (rs - rf)) • g))) ξ :=
    calc provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l
        = provingProb Astar (l + δ) - provingProb Astar l := h23
      _ = (provingProb Astar l + @inner ℝ _ _ g δ +
              1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • δ)) ξ) -
            provingProb Astar l := hL243
      _ = @inner ℝ _ _ g ((α * (rs - rf)) • g) +
            1 / 2 * deriv (deriv fun s : ℝ =>
              provingProb Astar (l + s • ((α * (rs - rf)) • g))) ξ := by
          -- [L24.4] = ∇_l p_kᵀ (α Δ_r ∇_l p_k) + ½ (α Δ_r ∇_l p_k)ᵀ (∇²_l p_s(ξ)) (α Δ_r ∇_l p_k)
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * - hδ
          aesop (config := {
              maxRuleApplications := 100
              maxRuleApplicationDepth := 10
              maxNormIterations := 320
              enableSimp := false
              useDefaultSimpSet := false
            })
              (add norm 100 (by norm_cast))
              (add norm 0 (by linarith))
              (add norm 0 (by nlinarith))
              (add norm 0 (by positivity))
              (add norm 0 (by omega))
              (add norm 1 (by push_neg))
              (add norm 0 (by bound))
              (add norm 0 (by ring_nf))
              (add norm 1 (by field_simp [*] at *))
              (add safe 100 (by ring))
              (add safe 100 (by field_simp))
              (add safe 100 (by norm_num))
              (add safe 100 (by interval_cases))
              (add safe 0 (by ext))
              (add safe 0 (by split))
              (add safe 100 (by rfl))
              (add safe 100 (by decide))
              (add safe 0 (by push_cast))
              (add safe 100 (by assumption_mod_cast))
              (add unsafe 10% (by exfalso))
              (add unsafe 90% (by norm_num [*] at *))
              (add norm 0 (by grind only [sub_smul]))
              (add norm 0 (by grind only [smul_add]))
              (add norm 0 (by grind only [smul_sub]))
              (add norm 0 (by grind only [mul_div_cancel]))
              (add norm 0 (by grind only [mul_div_cancel_left]))
              (add norm 0 (by grind only [add_smul]))
              (add norm 0 (by grind only [WeakFEPair.Λ]))
              (add norm 0 (by grind only [WeakFEPair.Λ₀_eq]))
              (add norm 0 (by grind only [smul_smul]))
              (add norm 0 (by grind only [Derivation.leibniz]))
              (add norm 0 (by grind only [div_mul]))
              (add norm 0 (by grind only [one_smul]))
              (add norm 0 (by grind only [two_smul]))
              (add norm 0 (by grind only [mul_div_cancel_right]))
              (add norm 0 (by grind only [MulAction]))
              (add norm 0 (by grind only [real_inner_smul_right]))
              (add norm 0 (by grind only [inner_]))
              (add norm 0 (by grind only [midpoint_add_sub]))
              (add norm 0 (by grind only [sub_div_sub_smul_slope_add_sub_div_sub_smul_slope]))
              (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux8]))
              (add norm 0 (by grind only [aux_sub]))
              (add norm 0 (by grind only [real_inner_smul_left]))
              (add norm 0 (by grind only [smul_eq_mul]))
              (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux7]))
              (add norm 0 (by grind only [WeakFEPair.Λ₀]))
              (add norm 0 (by grind only [AddConstMapClass.map_sub_zsmul]))
              (add norm 0 (by grind only [skewAdjointPart]))
              (add norm 0 (by grind only [Convex.add_smul]))
              (add norm 0 (by grind only [neg_smul]))
              (add norm 0 (by grind only [smul_neg]))
              (add safe 0 (by simp only [div_div] at *))
              (add safe 0 (by simp only [mul_div] at *))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   (linarith)
  -- [cite: norm_gradient_expectedReward_le] Lemma 2.3 at l_k: ‖∇_l J_sparse(l_k)‖₂ ≤ √(HM) Δ_r p_k
  have hL23 := norm_gradient_expectedReward_le Astar rs rf hr l
  -- [cite: provingProb_deriv2_bound] the bounded Hessian of the softmax at the point l_k + ξ δ: |δᵀ ∇²_l p_s δ| ≤ (4H + 1) ‖δ‖₂²
  have hD2 := provingProb_deriv2_bound hM Astar l δ ξ
  -- [aux, cite: provingProb_nonneg] p_k ≥ 0, so both sides of Lemma 2.3's bound are nonnegative when squared (used by L24.8)
  have hpnn : 0 ≤ provingProb Astar l := provingProb_nonneg Astar l
  -- the chain (2.3)–(2.8)
  have h28 : provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ≤
      α * (rs - rf) * ((H : ℝ) * M * provingProb Astar l ^ 2) +
        1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * H + 1) * ((H : ℝ) * M * provingProb Astar l ^ 2) :=
    calc provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l
        = @inner ℝ _ _ g ((α * (rs - rf)) • g) +
            1 / 2 * deriv (deriv fun s : ℝ =>
              provingProb Astar (l + s • ((α * (rs - rf)) • g))) ξ := h25
      _ ≤ α * (rs - rf) * ‖g‖ ^ 2 + 1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * H + 1) * ‖g‖ ^ 2 := by
          -- [L24.5 + L24.6 merged into L24.7: the skeleton has no Hessian, so ‖∇²_l p_s(ξ)‖₂ and xᵀ Q x ≤ ‖Q‖₂ ‖x‖₂² have no Lean counterpart; with ‖∇²_l p_s‖₂ ≤ 4H + 1 they are provingProb_deriv2_bound] ≤ α Δ_r ‖∇_l p_k‖₂² + ½ α² Δ_r² ‖∇²_l p_s(ξ)‖₂ ‖∇_l p_k‖₂² = α Δ_r ‖∇_l p_k‖₂² + O(α² ‖∇_l p_k‖₂²), the O-term explicit with ‖∇²_l p_s(ξ)‖₂ ≤ 4H + 1   (the bounded Hessian of the softmax)
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * - hD2 hδ
          rw [hδ] at hD2
          have hn : ‖(α * (rs - rf)) • g‖ ^ 2 = α ^ 2 * (rs - rf) ^ 2 * ‖g‖ ^ 2 := by
            rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
            ring
          have key : ∀ x : ℝ, x ≤ (4 * (H : ℝ) + 1) * ‖(α * (rs - rf)) • g‖ ^ 2 →
              inner ℝ g ((α * (rs - rf)) • g) + 1 / 2 * x ≤
                α * (rs - rf) * ‖g‖ ^ 2 + 1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * (H : ℝ) + 1) * ‖g‖ ^ 2 := by
            intro x hx
            rw [hn] at hx
            rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
            linarith
          exact key _ ((le_abs_self _).trans hD2)
      _ ≤ α * (rs - rf) * ((H : ℝ) * M * provingProb Astar l ^ 2) +
            1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * H + 1) *
              ((H : ℝ) * M * provingProb Astar l ^ 2) := by
          -- [L24.8] ≤ α Δ_r (HM · p_k²) + O(α² (HM · p_k²)), the O-term explicit   (Lemma 2.3)
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * - hL23 hS2 hα hr hpnn
          have hd : 0 < rs - rf := sub_pos.mpr hr
          have hn : ‖(rs - rf) • g‖ = (rs - rf) * ‖g‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
          rw [hS2, hn] at hL23
          clear hS2
          have hg : ‖g‖ ≤ Real.sqrt ((H : ℝ) * M) * provingProb Astar l := by
            by_contra hcon
            push_neg at hcon
            linarith [mul_lt_mul_of_pos_left hcon hd]
          have h0 : 0 ≤ ‖g‖ := norm_nonneg _
          have hs : Real.sqrt ((H : ℝ) * M) * Real.sqrt ((H : ℝ) * M) = (H : ℝ) * M :=
            Real.mul_self_sqrt (by positivity)
          have hsq : ‖g‖ ^ 2 ≤ (H : ℝ) * M * provingProb Astar l ^ 2 := by
            calc ‖g‖ ^ 2 = ‖g‖ * ‖g‖ := sq _
              _ ≤ (Real.sqrt ((H : ℝ) * M) * provingProb Astar l) *
                    (Real.sqrt ((H : ℝ) * M) * provingProb Astar l) := mul_self_le_mul_self h0 hg
              _ = Real.sqrt ((H : ℝ) * M) * Real.sqrt ((H : ℝ) * M) * provingProb Astar l ^ 2 := by ring
              _ = (H : ℝ) * M * provingProb Astar l ^ 2 := by rw [hs]
          have hA : 0 ≤ α * (rs - rf) := mul_nonneg hα.le hd.le
          have hB : 0 ≤ 1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * (H : ℝ) + 1) := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left hsq hA) (mul_le_mul_of_nonneg_left hsq hB)
  have hL249 : |1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • ((α * (rs - rf)) • g))) ξ| ≤
      @inner ℝ _ _ g ((α * (rs - rf)) • g) := by
    -- [L24.9] In (2.5), for small α, the first term dominates the second   (read as |second| ≤ first; small α is α ≤ 1/((4H + 1) Δ_r))
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hD2 hδ hα hαle hr
    have hc : 0 < α * (rs - rf) := mul_pos hα (sub_pos.mpr hr)
    have hH : (0:ℝ) < 4 * (H:ℝ) + 1 := by positivity
    have hcle : (4 * (H:ℝ) + 1) * (α * (rs - rf)) ≤ 1 := by
      have h1 := (le_div_iff₀ (mul_pos hH (sub_pos.mpr hr))).mp hαle
      linarith
    have ha : inner ℝ δ δ = ‖δ‖ ^ 2 := real_inner_self_eq_norm_sq δ
    have hb : inner ℝ δ δ = α * (rs - rf) * inner ℝ g δ := by
      rw [hδ]; exact real_inner_smul_left _ _ _
    have e1 : inner ℝ g δ = α * (rs - rf) * inner ℝ g g := by
      rw [hδ]; exact real_inner_smul_right _ _ _
    have e2 : inner ℝ g g = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
    have hX : 0 ≤ inner ℝ g δ := by
      rw [e1, e2]; exact mul_nonneg hc.le (sq_nonneg _)
    have hK : (4 * (H:ℝ) + 1) * ‖δ‖ ^ 2 ≤ inner ℝ g δ := by
      rw [← ha, hb]
      have h4 := mul_le_mul_of_nonneg_right hcle hX
      linarith
    try rw [← hδ]
    refine le_trans ?_ (hD2.trans hK)
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by norm_num)
  have hL2410 : provingProb Astar l ≤ provingProb Astar (ascentStep Astar rs rf α l) := by
    -- [L24.10] so p_{k+1} ≥ p_k
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - h25 hL249
    rw [sub_eq_iff_eq_add] at h25
    rw [abs_le] at hL249
    cases hL249
    linarith
  have hL2411 : 0 ≤ provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ∧
      provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ≤
        2 * α * ((H : ℝ) * M) * (rs - rf) * provingProb Astar l ^ 2 := by
    -- [L24.11] Thus, 0 ≤ p_{k+1} − p_k ≤ c · p_k², c ∈ O(α · HM · Δ_r), for a sufficiently small α   (here c = 2 α H M Δ_r and α ≤ 1/((4H + 1) Δ_r))
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hL2410 h28 hα hαle hr
    have hΔ : 0 < rs - rf := sub_pos.mpr hr
    have hK : 0 < (4 * (H : ℝ) + 1) * (rs - rf) := mul_pos (by positivity) hΔ
    have hαK : α * ((4 * (H : ℝ) + 1) * (rs - rf)) ≤ 1 := by
      exact (le_div_iff₀ hK).mp hαle
    have hX : 0 ≤ (H : ℝ) * M * provingProb Astar l ^ 2 := by positivity
    have hY : 0 ≤ α * (rs - rf) * ((H : ℝ) * M * provingProb Astar l ^ 2) :=
      mul_nonneg (mul_nonneg hα.le hΔ.le) hX
    have h1 := mul_le_mul_of_nonneg_right hαK hY
    refine ⟨sub_nonneg.mpr hL2410, ?_⟩
    linarith [h1, hY, h28]
  exact hL2411

end Sec2.DSP
