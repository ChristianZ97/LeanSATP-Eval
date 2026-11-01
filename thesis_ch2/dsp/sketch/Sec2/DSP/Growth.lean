import Sec2.Growth
import Sec2.DSP.ProveWith
import Sec2.DSP.SelfBound

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
          prove_with []
      _ = provingProb Astar (l + δ) - provingProb Astar l := by
          -- [L24.2] = p_s(l_k + δ) − p_s(l_k)
          prove_with [hS2, hδ]
  have hp2 : ContDiff ℝ 2 (provingProb Astar) := by
    -- [aux] p_s is C² in the logits: the Taylor expansion of (2.3)→(2.4) needs it (the thesis uses it silently)
    prove_with [hM]
  -- [aux, cite: differentiable_provingProb] p_s is differentiable, so ∇_l p_k is its gradient at l_k (used by L24.3)
  have hdp : Differentiable ℝ (provingProb Astar) := differentiable_provingProb Astar
  obtain ⟨ξ, hξ, hL243⟩ : ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      provingProb Astar (l + δ) - provingProb Astar l =
        (provingProb Astar l + @inner ℝ _ _ g δ +
            1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • δ)) ξ) -
          provingProb Astar l := by
    -- [L24.3] = (p_k + ∇_l p_kᵀ δ + ½ δᵀ (∇²_l p_s(ξ)) δ) − p_k   (Taylor expansion, for some ξ between l_k and l_k + δ; the point is l_k + ξ δ, and δᵀ ∇²_l p_s δ there is the second derivative of s ↦ p_s(l_k + s δ) at ξ)
    prove_with [hp2, hg, hdp]
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
          prove_with [hδ]
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
          prove_with [hD2, hδ]
      _ ≤ α * (rs - rf) * ((H : ℝ) * M * provingProb Astar l ^ 2) +
            1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * H + 1) *
              ((H : ℝ) * M * provingProb Astar l ^ 2) := by
          -- [L24.8] ≤ α Δ_r (HM · p_k²) + O(α² (HM · p_k²)), the O-term explicit   (Lemma 2.3)
          prove_with [hL23, hS2, hα, hr, hpnn]
  have hL249 : |1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • ((α * (rs - rf)) • g))) ξ| ≤
      @inner ℝ _ _ g ((α * (rs - rf)) • g) := by
    -- [L24.9] In (2.5), for small α, the first term dominates the second   (read as |second| ≤ first; small α is α ≤ 1/((4H + 1) Δ_r))
    prove_with [hD2, hδ, hα, hαle, hr]
  have hL2410 : provingProb Astar l ≤ provingProb Astar (ascentStep Astar rs rf α l) := by
    -- [L24.10] so p_{k+1} ≥ p_k
    prove_with [h25, hL249]
  have hL2411 : 0 ≤ provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ∧
      provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ≤
        2 * α * ((H : ℝ) * M) * (rs - rf) * provingProb Astar l ^ 2 := by
    -- [L24.11] Thus, 0 ≤ p_{k+1} − p_k ≤ c · p_k², c ∈ O(α · HM · Δ_r), for a sufficiently small α   (here c = 2 α H M Δ_r and α ≤ 1/((4H + 1) Δ_r))
    prove_with [hL2410, h28, hα, hαle, hr]
  exact hL2411

end Sec2.DSP
