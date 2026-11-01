# Thesis Chapter 2 ↔ Lean statements

The reference is Chapter 2 of the master's thesis; numbering follows the thesis, and the journal version uses the same numbers. The Lean files are in `project/Sec2/`. All statements are proved: as of 2026-11-01 there is no `sorry`, and only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) are used. This document confirms that what Lean proves is what the thesis states.

## Shared setup (`Sec2/Basic.lean`; the Setup remark in §2.2 of the thesis and Eq. (2.1))

| Thesis | Lean | Notes |
|---|---|---|
| A fixed context `C` | No definition takes `C` as an argument | From the Setup remark through Lemma 2.7, the thesis fixes one context (the future work mentioned in Remark 2.6 refers only to extending the `Ω(1/p_s)` bound of Prop 2.5 to `θ` and to many contexts). Only Corollary 2.8 has many contexts: in `RandomSearch.lean` they enter only through the per-context proving probabilities `p : ι → ℝ`, and these definitions are not used |
| `H` components, each with `M` levels (`M_h = M`) | `Arm H M := Fin H → Fin M` | Follows the simplification in the thesis's Setup remark |
| logits `l ∈ ℝ^{HM}` | `Logits H M := EuclideanSpace ℝ (Fin H × Fin M)` | Gradients and 2-norms use Mathlib's definitions. Mathlib's `gradient` is defined as 0 where the function is not differentiable; `differentiable_expectedReward` and `differentiable_provingProb` prove that `J_sparse` and `p_s` are differentiable everywhere (with no assumptions), so `gradient` is the thesis's `∇_l` |
| softmax `π^{(h)}(m∣C)` | `softmax l h m` | `exp(l_h^m) / Σ_{m'} exp(l_h^{m'})` |
| Eq. (2.1) `π(A∣C) = ∏_j π(v^lem_j∣C) · ∏_u π(v^tac_u∣C) · ∏_b π(v^budget_b∣C)` | `policy l A = ∏_h softmax l h (A h)` | The three groups of components share one index `h : Fin H` (`H = K + \|𝕋\| + B`), i.e., the `∏_h π^{(h)}(v_h∣C)` of the Setup remark and the proof of Lemma 2.3 |
| `p_s = Σ_{A∈𝒜*} π(A∣C)` | `provingProb Astar l` | `𝒜*` is a finite set of arms; it is assumed nonempty only where a theorem needs it |
| `R(C,A)`, `J_sparse = E[R]` | `reward`, `expectedReward` | The thesis defines `𝒜*` from `R`; here, conversely, `R` is defined from `𝒜*`. The two are equivalent when `r_success ≠ r_failure` |
| `J_sparse = Δ_r p_s + r_failure` | `expectedReward_eq` | `Δ_r = rs − rf` |
| `∇_l J_sparse = Δ_r ∇_l p_s` | `gradient_expectedReward` | Follows from `expectedReward_eq`; used by the first equality in the proof of Lemma 2.3 and by `δ = αΔ_r ∇_l p_k` in the proof of Lemma 2.4 |
| Chain rule `‖∇_θ J_sparse‖₂ ≤ ‖∂l/∂θ‖₂ · ‖∇_l J_sparse‖₂` | `norm_gradient_comp_le` | `net : ℝ^d → ℝ^{HM}` is the network's map for a fixed `C`, assumed differentiable at `θ` (where it is not differentiable, Mathlib's `fderiv` is 0); `‖∂l/∂θ‖₂ = ‖fderiv ℝ net θ‖` is the operator norm, which is a real number and hence finite. The results from Lemma 2.3 to Remark 2.6 are all stated for `l`; the only links to `θ` are this one and the Proof sketch's θ version `norm_gradient_expectedReward_comp_le` |
| `J*_sparse = sup_l J_sparse` | `optReward` (in `Sec2/Plateau.lean`) | `⨆` on ℝ; `J_sparse` is bounded above, so this is the true sup |

Further basic properties: `softmax_pos`, `sum_softmax`, `policy_pos`, `sum_policy`, `provingProb_nonneg`, `provingProb_pos`, `provingProb_le_one`, `differentiable_provingProb`, `differentiable_expectedReward`.

How assumptions are written (the same in every file): `hM : 0 < M` is the thesis's `M ≥ 1` (level 0 always exists); `hA : Astar.Nonempty` is the Setup remark's `𝒜* ≠ ∅`; `hr : rf < rs` is `Δ_r > 0`; `hq0` and `hq1` are `q ∈ (0,1)`. Only `sum_softmax`, `sum_policy` and `expectedReward_eq` would be false without `hM`; the other theorems carry `hM` only to keep the thesis's `M ≥ 1`, which does not change their meaning.

## Lemma 2.3 Self-bounding gradient (`Sec2/SelfBound.lean`)

- **Thesis:** `‖∇_l J_sparse‖₂ ≤ √(HM) · Δ_r · p_s`.
- **Lean:** `norm_gradient_expectedReward_le`. For all `l`, `‖gradient J l‖ ≤ √(H·M) · (rs − rf) · p_s(l)`.
- **Differences:** None.
- **θ version (Proof sketch):** The thesis says "`‖∇_θ p_s‖₂` is at most a constant times `p_s` (see Lemma 2.3)". Lean: `norm_gradient_expectedReward_comp_le`, which states that when `net` is differentiable at `θ`, `‖∇_θ J‖₂ ≤ ‖∂l/∂θ‖₂ · √(HM) · Δ_r · p_s`; the constant contains `‖∂l/∂θ‖₂` and varies with `θ`.

## Lemma 2.4 Quadratic per-step growth (`Sec2/Growth.lean`)

- **Thesis:** Gradient ascent on `l`: `l_{k+1} = l_k + α ∇_l J_sparse(l_k)`. With a sufficiently small step size, `0 ≤ p_{k+1} − p_k ≤ c · p_k²`, `c ∈ O(α · HM · Δ_r)`.
- **Lean:**
  - `ascentStep Astar rs rf α l = l + α • ∇_l J_sparse(l)`: one step of gradient ascent.
  - `growth`: for all `0 < α ≤ α₀ = 1/((4H+1)·Δ_r)` and all `l`, after one step `0 ≤ p' − p ≤ 2α·HM·Δ_r · p²`.
- **Differences:** The thesis's "sufficiently small" and `O(·)` are written here as explicit quantities:
  - `α₀ = 1/((4H+1)·Δ_r)` depends only on `H` and `Δ_r`, not on `l`, `M` or `𝒜*` (`4H+1` is the constant of `provingProb_deriv2_bound`);
  - `c = 2α·HM·Δ_r`, i.e., the constant in the O is taken to be 2;
  - the thesis states the result for the sequence `l_k`, while Lean states one step from an arbitrary `l`; taking `l = l_k` gives every `k`.
- **Added proof:** In the thesis's proof, "the bounded Hessian of the softmax" is not proved; here it is `provingProb_deriv2_bound`: along any direction `δ`, the second derivative of `t ↦ p_s(l + tδ)` has absolute value ≤ `(4H+1)‖δ‖²`. This is equivalent to `‖∇²_l p_s‖₂ ≤ 4H+1`. It is an internal step of the proof; `4H+1` is a coarse constant that is easy to prove (not the best constant), and the `α₀` of `growth`, `plateau` and `plateau_uniform` uses the same constant, so changing it means changing all three together.

## Proposition 2.5 Sparsity inflates verification cost (`Sec2/Plateau.lean`)

- **Thesis:** With `c` as in Lemma 2.4:
  - For all `k ≤ k̄ = 1/(2c p_0)`, `J* − J(l_k) = Δ_r(1 − p_k) ≥ Δ_r(1 − 2p_0)`.
  - With `Θ(1)` verifications per step, `N(ε) ∈ Ω(1/p_0)` for any `ε < Δ_r(1 − 2p_0)`.
- **Lean:**
  - `ascent Astar rs rf α l₀ k`: the `l_k` obtained from `l₀` by `k` applications of `ascentStep`.
  - `optReward`: `J* = sup_l J_sparse(l)`. `optReward_eq`: `J* = r_success`, which is the `sup_l p_s = 1` of the thesis's proof; it needs `𝒜*` to be nonempty.
  - `plateau`: the step-size condition and `c` are the same as in `growth`. For all `0 < α ≤ α₀ = 1/((4H+1)·Δ_r)` and all starting points `l₀`, with `c = 2α·HM·Δ_r` and `p₀ = p_s(l₀)`:
    1. for all `k ≤ 1/(2c·p₀)`, `J* − J(l_k) = Δ_r(1 − p_k)`, and this is `≥ Δ_r(1 − 2p₀)`;
    2. for all `ε < Δ_r(1 − 2p₀)`, every number of steps `k` with `J* − J(l_k) ≤ ε` is `> 1/(2c·p₀)`;
    3. if `V k` is the cumulative verification count after `k` steps, with at least one verification per step (`k ≤ V k`), then `V k > 1/(2c·p₀)` when `ε`-suboptimality is reached.
  - `plateau` additionally assumes `H > 0`, to rule out Lean's `1/0 = 0` when `c = 0`.
- **Differences:** The thesis's `N(ε) ∈ Ω(1/p_0)` is written as the explicit lower bound `1/(2c·p₀) = 1/(4α·HM·Δ_r·p₀)` in items 2 and 3 (with `α`, `H`, `M`, `Δ_r` fixed). Item 3 expresses "Θ(1) verifications per step" through the cumulative verification count `V`; the lower bound needs only "at least one per step".

## Remark 2.6 Implication (`Sec2/Plateau.lean`; the last sentence in `Sec2/RandomSearch.lean`)

- **Thesis:** At a uniform initialization, `π^{(h)}(m∣C) = 1/M`, `p_0 = |𝒜*| M^{−H}`, and `π(·∣C)` is uniform over `𝒜`. If `|𝒜*|` is bounded and `M ≥ 2`, `k̄ = 1/(2c·p_0)` is exponential in `H`; a single component (`H = 1`) with a single optimal arm (`|𝒜*| = 1`) has `p_0 = 1/M`. Uniform random search also has proving probability `p_0` and, by Lemma 2.7, needs `Θ(1/p_0)` verifications.
- **Lean:**
  - `policy_of_uniform`, `provingProb_of_uniform`: the hypothesis is exactly the thesis's "`π^{(h)}(m∣C) = 1/M` for every `h` and `m`", and the conclusions are that each arm has probability `1/M^H` (uniform over `𝒜`) and that `p_s = |𝒜*| / M^H`;
  - `softmax_zero`: all-zero logits satisfy this hypothesis;
  - `policy_zero`, `provingProb_zero`: the special case `l = 0`;
  - `plateau_uniform`: starting from a uniformly initialized `l₀` (with the same step-size condition as `growth` and `plateau`), every number of steps that reaches ε-suboptimality satisfies `k > M^H/(2c·|𝒜*|)`, where `c = 2α·HM·Δ_r`;
  - `provingProb_zero_single`: `p_0 = 1/M` when `H = 1` and `|𝒜*| = 1`;
  - `uniformSearch_bounds` (`Sec2/RandomSearch.lean`): the last sentence. It is `minSamples_bounds` with `p := p_s(0)`: `q/p_0 ≤ N ≤ (−log(1−q)+1)/p_0`, with constants independent of `H`, `M` and `𝒜*`.
- **Assumptions:** Remark 2.6 states the assumptions of its two Implication sentences, and the Lean versions match them:
  - "If `|𝒜*|` is bounded and `M ≥ 2`, `k̄` is exponential in `H`": `plateau_uniform` gives `k̄ = M^H/(2c·|𝒜*|)` explicitly, which grows exponentially in `H` under these assumptions. They are needed: `𝒜* = {A : A_0 = 1}` has `M^{H−1}` arms, `p_0 = 1/M`, and `k̄ = 1/(4α·H·Δ_r)` decreases as `H` grows.
  - "A single component with a single optimal arm has `p_0 = 1/M`": `provingProb_zero_single`, with the hypotheses `H = 1` and `|𝒜*| = 1`. Without the second, `p_0 = |𝒜*|/M ≥ 1/M`.

## Lemma 2.7 Random search costs `Θ(1/p_s)` (`Sec2/RandomSearch.lean`)

- **Thesis:** For a fixed `q ∈ (0,1)`, the smallest number of independent samples with "probability of at least one success ≥ q" satisfies `N ∈ Θ(1/p_s)` (`p_s → 0`). The proof gives the finer result `N = −log(1−q)/p_s · (1 + O(p_s))`.
- **Lean:**
  - `minSamples q p`: the smallest `N` with `1 − (1−p)^N ≥ q`. By design, it starts from "the probability that all samples fail is `(1−p)^N`" and does not formalize the product measure.
  - `minSamples_spec`: it is indeed the smallest.
  - `minSamples_isTheta`: `N =Θ[p→0⁺] 1/p`.
  - `minSamples_sub_isBigO`: `N − (−log(1−q))/p = O(1)`, which is equivalent to the thesis's `(1 + O(p))` form.
  - `minSamples_bounds`: for `p ∈ (0, 1]`, `q/p ≤ N ≤ (−log(1−q)+1)/p`.
- **Differences:**
  - The thesis's distribution `π(·∣C)` and `p_s = Σ_{A∈𝒜*} π(A∣C)` do not appear in Lean; `p` is just a real number. `N` depends on `π` only through `p_s`, and the theorems hold for every `p` in the range, so they cover any fixed distribution.
  - `minSamples_bounds` is an explicit-constant version that the thesis does not have (the thesis has only Θ and `1 + O(p_s)`).

## Corollary 2.8 Cost of per-context search (`Sec2/RandomSearch.lean`)

- **Thesis:** A finite context set, with per-context proving probabilities `p_C`. Obtaining a successful configuration for each context separately, with probability at least `q`, requires `N_𝒞 ∈ Θ(Σ_C 1/p_C)` verifications. The first step of the proof is "the contexts are searched independently, so `N_𝒞 = Σ_C N_C`"; Lemma 2.7 is then applied to each `C`.
- **Lean:**
  - `perContext_minTotal`: when each context reaches `q` on its own, the smallest total verification count is `Σ_C N_C` (`N_C = minSamples q p_C`), which is the first step of the proof.
  - `perContext_bounds`: when all `p_C ∈ (0, 1]`, `q·Σ 1/p_C ≤ Σ N_C ≤ (−log(1−q)+1)·Σ 1/p_C`, which is `minSamples_bounds` summed over all `C`.
- **Differences:**
  - The thesis's Θ states no constants and does not restrict `p_C`. Here the constants depend only on `q`, not on the number of contexts or on any `p_C`. The lower-bound constant `q` comes from the union bound: the probability that `N` samples yield at least one success is ≤ `N·p_C`.
  - "With probability at least `q`" is a requirement on each context separately, following the reading of the thesis's proof. If it were read as "all contexts succeed simultaneously", the total count would be larger by a factor of about `log|𝒞|`, and the constants could no longer be independent of the number of contexts.
  - One sample counts as one verification (as for `N` in the Ch. 5 notation table).

## Points to confirm

1. Lemma 2.4 takes `c` to be `2α·HM·Δ_r` (O constant 2), with the step-size upper bound `α₀ = 1/((4H+1)·Δ_r)`; `plateau` for Prop 2.5 and `plateau_uniform` for Remark 2.6 use the same step-size upper bound and `c`.
2. The `Ω(1/p_0)` of Prop 2.5 is expressed as "number of steps > `1/(2c·p₀)`" and "cumulative verification count > `1/(2c·p₀)` (at least one verification per step)"; `plateau` additionally assumes `H > 0`.
3. Cor 2.8 expresses Θ with the constants `q` and `−log(1−q)+1`, which depend only on `q`, with no range assumed beyond `p_C ∈ (0, 1]`; `N_𝒞 = Σ_C N_C` is written as `perContext_minTotal`.
4. The two Implication sentences of Remark 2.6 are written as `plateau_uniform` and `provingProb_zero_single`, with the assumptions that Remark 2.6 states (`|𝒜*|` bounded and `M ≥ 2`; `|𝒜*| = 1`); see Remark 2.6 above.
5. The network parameters `θ` are in scope: the Setup remark's chain rule `norm_gradient_comp_le` and the Proof sketch's θ version `norm_gradient_expectedReward_comp_le` are added together; if `θ` is left out of scope, both are moved together to "not formalized".
