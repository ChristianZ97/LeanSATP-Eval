import Sec2.Basic
import Sec2.DSP.ProveWith

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
  have hS1 : expectedReward Astar rs rf l = (rs - rf) * provingProb Astar l + rf := by prove_with [hM, hsum]
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
  have hS2 : gradient (expectedReward Astar rs rf) l = (rs - rf) • gradient (provingProb Astar) l := by prove_with [hS1, hdiff]
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
  have hS3 : ‖gradient (fun θ' => expectedReward Astar rs rf (net θ')) θ‖ ≤ ‖fderiv ℝ net θ‖ * ‖gradient (expectedReward Astar rs rf) (net θ)‖ := by prove_with [hnet, hJdiff]
  exact hS3

end Sec2.DSP
