import Sec2.SelfBound
import Sec2.DSP.ProveWith
import Sec2.DSP.Basic

open Finset

namespace Sec2.DSP

variable {H M : ℕ}

/-- Lemma 2.3: for any logits `l`, `‖∇_l J_sparse(l)‖₂ ≤ √(HM) · Δ_r · p_s(l)`. -/
theorem norm_gradient_expectedReward_le (Astar : Finset (Arm H M)) (rs rf : ℝ) (hr : rf < rs)
    (l : Logits H M) :
    ‖gradient (expectedReward Astar rs rf) l‖ ≤
      Real.sqrt ((H : ℝ) * M) * (rs - rf) * provingProb Astar l := by
  -- [aux, cite: differentiable_provingProb] π(A|C) is p_s for 𝒜* = {A}, so it is differentiable in l (used by L23.2)
  have hdiffπ : ∀ A : Arm H M, Differentiable ℝ (provingProb {A}) :=
    fun A => differentiable_provingProb {A}
  -- [aux, cite: policy_pos] π(A|C) > 0 for every arm (used by L23.7)
  have hπ : ∀ A : Arm H M, 0 < policy l A := fun A => policy_pos l A
  -- l.81–88, for every h and m; ∂_{l_h^m} f is rendered as `fderiv ℝ f l (EuclideanSpace.single (h, m) 1)`
  have hpartial : ∀ (h : Fin H) (m : Fin M),
      |fderiv ℝ (provingProb Astar) l (EuclideanSpace.single (h, m) (1 : ℝ))| ≤
        provingProb Astar l := by
    intro h m
    have hL1 : ∀ (l₁ : Logits H M) (h' : Fin H), h' ≠ h → ∀ (v : Fin M) (t : ℝ),
        softmax (l₁ + t • EuclideanSpace.single (h, m) (1 : ℝ)) h' v = softmax l₁ h' v := by
      -- [L23.1] each entry l_h^m enters only π^(h) in π(A|C) = ∏_{h'} π^(h')(v_{h'}|C): changing l_h^m (l ↦ l + t·e_{(h,m)}) leaves π^(h') unchanged for h' ≠ h
      prove_with []
    have hL5 : ∀ A : Arm H M,
        (∏ h' ∈ Finset.univ.erase h, softmax l h' (A h')) * softmax l h (A h) = policy l A := by
      -- [L23.5] ∏_{h'≠h} π^(h')(v_{h'}|C) · π^(h)(v_h|C) = π(A|C)   (the underbrace of l.86)
      prove_with []
    -- [aux, cite: softmax_pos] π^(h)(m'|C) > 0 for every level m' (used by L23.8)
    have hsm : ∀ m' : Fin M, 0 < softmax l h m' := fun m' => softmax_pos l h m'
    -- [aux, cite: sum_softmax] Σ_{m'} π^(h)(m'|C) = 1 when 0 < M (used by L23.8)
    have hsum : 0 < M → ∑ m' : Fin M, softmax l h m' = 1 := fun hM => sum_softmax hM l h
    have hL8 : ∀ A : Arm H M, |(if A h = m then (1 : ℝ) else 0) - softmax l h m| ≤ 1 := by
      -- [L23.8] |1(·) − π^(h)(m|C)| ≤ 1, with 1(·) = 1(v_h = m)
      prove_with [hsm, hsum]
    calc |fderiv ℝ (provingProb Astar) l (EuclideanSpace.single (h, m) (1 : ℝ))|
        _ = |∑ A ∈ Astar, fderiv ℝ (fun l' : Logits H M => ∏ h' : Fin H, softmax l' h' (A h')) l
              (EuclideanSpace.single (h, m) (1 : ℝ))| := by
          -- [L23.2] |∂_{l_h^m} p_s| = |Σ_{A∈𝒜*} ∂_{l_h^m} ∏_{h'} π^(h')(v_{h'}|C)|
          prove_with [hdiffπ]
        _ = |∑ A ∈ Astar, (∏ h' ∈ Finset.univ.erase h, softmax l h' (A h')) *
              fderiv ℝ (fun l' : Logits H M => softmax l' h (A h)) l
                (EuclideanSpace.single (h, m) (1 : ℝ))| := by
          -- [L23.3] = |Σ_{A∈𝒜*} (∏_{h'≠h} π^(h')(v_{h'}|C)) · ∂_{l_h^m} π^(h)(v_h|C)|   (only π^(h) depends on l_h^m)
          prove_with [hL1]
        _ = |∑ A ∈ Astar, ((∏ h' ∈ Finset.univ.erase h, softmax l h' (A h')) * softmax l h (A h)) *
              ((if A h = m then (1 : ℝ) else 0) - softmax l h m)| := by
          -- [L23.4] = |Σ_{A∈𝒜*} (∏_{h'≠h} π^(h')(v_{h'}|C) · π^(h)(v_h|C)) · (1(v_h = m) − π^(h)(m|C))|   (the softmax derivative)
          prove_with []
        _ = |∑ A ∈ Astar, policy l A * ((if A h = m then (1 : ℝ) else 0) - softmax l h m)| := by
          -- [L23.6] = |Σ_{A∈𝒜*} π(A|C) · (1(v_h = m) − π^(h)(m|C))|   (the underbrace)
          prove_with [hL5]
        _ ≤ ∑ A ∈ Astar, policy l A := by
          -- [L23.7] ≤ Σ_{A∈𝒜*} π(A|C)   (the triangle inequality and L23.8)
          prove_with [hL8, hπ]
        _ = provingProb Astar l := by
          -- [L23.9] Σ_{A∈𝒜*} π(A|C) = p_s
          prove_with []
  -- [aux, cite: gradient_expectedReward] ∇_l J_sparse = Δ_r ∇_l p_s when 0 < M (used by L23.10)
  have hgradJ : 0 < M →
      gradient (expectedReward Astar rs rf) l = (rs - rf) • gradient (provingProb Astar) l :=
    fun hM => gradient_expectedReward hM Astar rs rf l
  -- [aux, cite: provingProb_nonneg] p_s ≥ 0 (used by L23.13)
  have hps : 0 ≤ provingProb Astar l := provingProb_nonneg Astar l
  have hentry : ∀ (h : Fin H) (m : Fin M),
      (gradient (provingProb Astar) l) (h, m) =
        fderiv ℝ (provingProb Astar) l (EuclideanSpace.single (h, m) (1 : ℝ)) := by
    -- [aux] the (h, m) entry of ∇_l p_s equals the rendering of ∂_{l_h^m} p_s used above (fderiv along EuclideanSpace.single (h, m) 1)
    prove_with []
  -- l.90–97: summing the HM squared partial derivatives
  calc ‖gradient (expectedReward Astar rs rf) l‖
      _ = (rs - rf) * ‖gradient (provingProb Astar) l‖ := by
        -- [L23.10] ‖∇_l J_sparse‖₂ = Δ_r ‖∇_l p_s‖₂   (the Setup's ∇_l J_sparse = Δ_r ∇_l p_s, and Δ_r > 0)
        prove_with [hr, hgradJ]
      _ = (rs - rf) * Real.sqrt (∑ h : Fin H, ∑ m : Fin M,
            (fderiv ℝ (provingProb Astar) l (EuclideanSpace.single (h, m) (1 : ℝ))) ^ 2) := by
        -- [L23.11] = Δ_r √(Σ_{h,m} (∂_{l_h^m} p_s)²)   (summing the HM squared partial derivatives)
        prove_with [hentry]
      _ ≤ (rs - rf) * Real.sqrt (∑ h : Fin H, ∑ m : Fin M, provingProb Astar l ^ 2) := by
        -- [L23.12] ≤ Δ_r √(Σ_{h,m} p_s²)   (|∂_{l_h^m} p_s| ≤ p_s for every h and m)
        prove_with [hr, hpartial]
      _ = Real.sqrt ((H : ℝ) * M) * (rs - rf) * provingProb Astar l := by
        -- [L23.13] = √(HM) Δ_r p_s
        prove_with [hps]

/-- The θ version in the Proof sketch (the Setup's chain rule combined with Lemma 2.3):
the network `net : ℝ^d → ℝ^{HM}` maps the parameters `θ` to the logits; if `net` is
differentiable at `θ`, then `‖∇_θ J_sparse‖₂ ≤ ‖∂l/∂θ‖₂ · √(HM) · Δ_r · p_s`.
Here `‖∂l/∂θ‖₂` is the operator norm of `fderiv ℝ net θ` and varies with `θ`.
Taking `rs = 1` and `rf = 0` gives the `p_s` version. -/
theorem norm_gradient_expectedReward_comp_le {d : ℕ} (Astar : Finset (Arm H M)) (rs rf : ℝ)
    (hr : rf < rs) (net : EuclideanSpace ℝ (Fin d) → Logits H M)
    (θ : EuclideanSpace ℝ (Fin d)) (hnet : DifferentiableAt ℝ net θ) :
    ‖gradient (fun θ' => expectedReward Astar rs rf (net θ')) θ‖ ≤
      ‖fderiv ℝ net θ‖ * (Real.sqrt ((H : ℝ) * M) * (rs - rf) * provingProb Astar (net θ)) := by
  -- [S.3, cite: norm_gradient_comp_le] at θ: ‖∇_θ J_sparse‖₂ ≤ ‖∂l/∂θ‖₂ · ‖∇_l J_sparse‖₂   (the chain rule)
  have hS3 := norm_gradient_comp_le Astar rs rf net θ hnet
  -- [Lemma 2.3, cite: norm_gradient_expectedReward_le] at l = net θ: ‖∇_l J_sparse‖₂ ≤ √(HM) · Δ_r · p_s
  have hL23 := norm_gradient_expectedReward_le Astar rs rf hr (net θ)
  have hPS1 : ‖gradient (fun θ' => expectedReward Astar rs rf (net θ')) θ‖ ≤
      ‖fderiv ℝ net θ‖ * (Real.sqrt ((H : ℝ) * M) * (rs - rf) * provingProb Astar (net θ)) := by
    -- [PS.1] ‖∇_θ p_s‖₂ is at most a constant times p_s: ‖∇_θ J_sparse‖₂ ≤ ‖∂l/∂θ‖₂ · (√(HM) Δ_r p_s)   (the two cites above)
    prove_with [hS3, hL23]
  exact hPS1

end Sec2.DSP
