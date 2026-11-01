import Sec2.Basic

set_option maxHeartbeats 0

open Finset

namespace Sec2.DSP

variable {H M : ℕ}

/-- Setup: with the context fixed, `J_sparse = Δ_r · p_s + r_failure`, where
`Δ_r = r_success − r_failure`. -/
theorem expectedReward_eq (hM : 0 < M) (Astar : Finset (Arm H M)) (rs rf : ℝ) (l : Logits H M) :
    expectedReward Astar rs rf l = (rs - rf) * provingProb Astar l + rf := by
  -- [aux, cite: sum_policy] Σ_A π(A|C) = 1, i.e., π(·|C) is a distribution over 𝒜 (used by S.1)
  have hsum : ∑ A : Arm H M, policy l A = 1 := sum_policy hM l
  -- [S.1] J_sparse = Δ_r p_s + r_failure   (with C fixed)
  have hS1 : expectedReward Astar rs rf l = (rs - rf) * provingProb Astar l + rf := by
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hM hsum
    unfold expectedReward provingProb
    rw [← Finset.sum_add_sum_compl Astar] at hsum ⊢
    have e1 : ∑ A ∈ Astar, policy l A * reward Astar rs rf A = ∑ A ∈ Astar, policy l A * rs :=
      Finset.sum_congr rfl fun A hA => by simp [reward, hA]
    have e2 : ∑ A ∈ Astarᶜ, policy l A * reward Astar rs rf A = ∑ A ∈ Astarᶜ, policy l A * rf :=
      Finset.sum_congr rfl fun A hA => by simp [reward, Finset.mem_compl.mp hA]
    rw [e1, e2, ← Finset.sum_mul, ← Finset.sum_mul]
    linear_combination rf * hsum
  exact hS1

/-- Setup: `∇_l J_sparse = Δ_r ∇_l p_s` (by `expectedReward_eq`). -/
theorem gradient_expectedReward (hM : 0 < M) (Astar : Finset (Arm H M)) (rs rf : ℝ)
    (l : Logits H M) :
    gradient (expectedReward Astar rs rf) l = (rs - rf) • gradient (provingProb Astar) l := by
  -- [S.1, cite: expectedReward_eq] J_sparse = Δ_r p_s + r_failure, for every l (as functions of l)
  have hS1 : expectedReward Astar rs rf = fun l' : Logits H M => (rs - rf) * provingProb Astar l' + rf :=
    funext (expectedReward_eq hM Astar rs rf)
  -- [aux, cite: differentiable_provingProb] p_s is differentiable at l; differentiating S.1 term by term needs it in Lean
  have hdiff : DifferentiableAt ℝ (provingProb Astar) l := differentiable_provingProb Astar l
  -- [S.2] ∇_l J_sparse = Δ_r ∇_l p_s   (hence, from S.1)
  have hS2 : gradient (expectedReward Astar rs rf) l = (rs - rf) • gradient (provingProb Astar) l := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - hS1 hdiff
    ext
    simp [hS1, gradient, hdiff, fderiv_const_mul]
  exact hS2

/-- The chain rule of the Setup: `net` is the network's map from the parameters `θ ∈ ℝ^d` to
the logits for a fixed context, and it is differentiable at `θ`.
`‖∇_θ J_sparse‖₂ ≤ ‖∂l/∂θ‖₂ · ‖∇_l J_sparse‖₂`, where `‖∂l/∂θ‖₂ = ‖fderiv ℝ net θ‖` is the
operator norm of the Jacobian (i.e., the spectral norm). It is a real number, so the thesis's
"finite for a fixed network" needs no separate statement. -/
theorem norm_gradient_comp_le {d : ℕ} (Astar : Finset (Arm H M)) (rs rf : ℝ)
    (net : EuclideanSpace ℝ (Fin d) → Logits H M) (θ : EuclideanSpace ℝ (Fin d))
    (hnet : DifferentiableAt ℝ net θ) :
    ‖gradient (fun θ' => expectedReward Astar rs rf (net θ')) θ‖ ≤
      ‖fderiv ℝ net θ‖ * ‖gradient (expectedReward Astar rs rf) (net θ)‖ := by
  -- [aux, cite: differentiable_expectedReward] J_sparse is differentiable at l = net θ; the chain rule needs it
  have hJdiff : DifferentiableAt ℝ (expectedReward Astar rs rf) (net θ) := differentiable_expectedReward Astar rs rf (net θ)
  -- [S.3] ‖∇_θ J_sparse‖₂ ≤ ‖∂l/∂θ‖₂ · ‖∇_l J_sparse‖₂   (the chain rule)
  have hS3 : ‖gradient (fun θ' => expectedReward Astar rs rf (net θ')) θ‖ ≤ ‖fderiv ℝ net θ‖ * ‖gradient (expectedReward Astar rs rf) (net θ)‖ := by
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hnet hJdiff
    have hc : HasFDerivAt (fun θ' => expectedReward Astar rs rf (net θ'))
        ((fderiv ℝ (expectedReward Astar rs rf) (net θ)).comp (fderiv ℝ net θ)) θ :=
      hJdiff.hasFDerivAt.comp θ hnet.hasFDerivAt
    have e1 : ‖gradient (fun θ' => expectedReward Astar rs rf (net θ')) θ‖ =
        ‖fderiv ℝ (fun θ' => expectedReward Astar rs rf (net θ')) θ‖ := by
      rw [gradient]
      exact LinearIsometryEquiv.norm_map _ _
    have e2 : ‖gradient (expectedReward Astar rs rf) (net θ)‖ =
        ‖fderiv ℝ (expectedReward Astar rs rf) (net θ)‖ := by
      rw [gradient]
      exact LinearIsometryEquiv.norm_map _ _
    rw [e1, e2, hc.fderiv, mul_comm]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  exact hS3

end Sec2.DSP
