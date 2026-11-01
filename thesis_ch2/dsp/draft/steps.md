# Thesis Chapter 2: the informal proof, step by step (draft for the DSP run)

This file is the *draft* of the DSP run. It splits the thesis's own proofs into numbered steps.
The sketch turns every step into one Lean `have` (or one `calc` link, or one `obtain`).

## Source

- Thesis Chapter 2, Section 2.2, "Reward Sparsity Induces an Optimization Plateau", as revised
  on 2026-11-01 (the Remark 2.6 premises were added).
- File: `paper/ch2.tex`. Every step below gives its line number in that file.
- Unicode renderings: `π^(h)(m|C)` is the softmax of component `h`, `∂_{l_h^m}` is the partial
  derivative in the entry `l_h^m`, and `1(·)` is the indicator.

## What counts as a step

1. A step is one of:
   - one formula or sentence that a proof asserts;
   - one link (`=`, `≤`, `≥`, `→`) of a displayed chain;
   - one formula given as a justification, for example `|1(·) − π^(h)(m|C)| ≤ 1`.
2. A named principle without a formula is not a step. It justifies the step it is attached to,
   and it goes into that step's comment. Examples: "the triangle inequality", "Taylor expansion",
   "the chain rule", "telescoping", "the softmax derivative".
3. Labels used below:
   - **cite**: the step is the thesis citing one of its own results ("By Lemma 2.4"). The sketch
     closes it with the cited public theorem, applied to arguments.
   - **model**: the step is how the Lean statements model the situation. It is not a step of the
     sketch.
   - **conclusion**: the theorem's goal. When the last thesis step is not literally the Lean
     goal, the goal is closed by one more gap with this label.

## Scope

17 of the 30 public theorems are asserted or proved in Section 2.2. They are listed below in
thesis order.

The other 13 have no proof in the thesis:

- `softmax_pos`, `sum_softmax`, `policy_pos`, `sum_policy`
- `provingProb_nonneg`, `provingProb_pos`, `provingProb_le_one`
- `differentiable_provingProb`, `differentiable_expectedReward`
- `provingProb_deriv2_bound`, `softmax_zero`
- `minSamples_spec`, `minSamples_bounds`

A sketch may cite them, and may cite any earlier theorem of this list.

`policy_zero` and `provingProb_zero` are term-mode corollaries of `policy_of_uniform` and
`provingProb_of_uniform`, which are in scope. Cite those two theorems, together with `softmax_zero`,
instead of the corollaries.

---

## 1. `expectedReward_eq` (Setup, l.67)

- **S.1** (l.67): "With C fixed, J_sparse = Δ_r p_s + r_failure." The step is the whole statement.

## 2. `gradient_expectedReward` (Setup, l.67)

- cite: S.1 (`expectedReward_eq`).
- **S.2** (l.67): "Hence ∇_l J_sparse = Δ_r ∇_l p_s." The step is the whole statement.

## 3. `norm_gradient_comp_le` (Setup, l.67–71)

- **S.3** (l.67–71): "By the chain rule, ‖∇_θ J_sparse‖₂ ≤ ‖∂l/∂θ‖₂ · ‖∇_l J_sparse‖₂."
  - Justification: the chain rule.
  - The step is the whole statement.
- l.72, "The first factor is finite for a fixed network", is not a step. In Lean, `‖∂l/∂θ‖₂` is
  a real number (see the docstring).

## 4. `norm_gradient_expectedReward_le` (Lemma 2.3, l.80–98)

- **L23.1** (l.81): "Each entry l_h^m enters only π^(h) in π(A|C) = ∏_{h'} π^(h')(v_{h'}|C)."
  - That is, changing `l_h^m` does not change `π^(h')` for `h' ≠ h`.
- "Hence, for every l, each partial derivative of p_s obeys" (l.81–88), for every `h` and `m`:
  - **L23.2** (l.83–84): `|∂_{l_h^m} p_s| = |Σ_{A∈𝒜*} ∂_{l_h^m} ∏_{h'} π^(h')(v_{h'}|C)|`
  - **L23.3** (l.85): `= |Σ_{A∈𝒜*} (∏_{h'≠h} π^(h')(v_{h'}|C)) · ∂_{l_h^m} π^(h)(v_h|C)|`
  - **L23.4** (l.86): `= |Σ_{A∈𝒜*} (∏_{h'≠h} π^(h')(v_{h'}|C) · π^(h)(v_h|C)) · (1(v_h = m) − π^(h)(m|C))|`
    - Justification (l.90): the softmax derivative.
  - **L23.5** (l.86, the underbrace): `∏_{h'≠h} π^(h')(v_{h'}|C) · π^(h)(v_h|C) = π(A|C)`
  - **L23.6** (l.87): `= |Σ_{A∈𝒜*} π(A|C) · (1(v_h = m) − π^(h)(m|C))|`
  - **L23.7** (l.88): `≤ Σ_{A∈𝒜*} π(A|C)`
    - Justification (l.90): the triangle inequality and L23.8.
  - **L23.8** (l.90): `|1(·) − π^(h)(m|C)| ≤ 1`
  - **L23.9** (l.88): `Σ_{A∈𝒜*} π(A|C) = p_s`
- "Summing the HM squared partial derivatives gives" (l.90–97):
  - **L23.10** (l.92–93): `‖∇_l J_sparse‖₂ = Δ_r ‖∇_l p_s‖₂`
  - **L23.11** (l.94): `= Δ_r √(Σ_{h,m} (∂_{l_h^m} p_s)²)`
  - **L23.12** (l.95): `≤ Δ_r √(Σ_{h,m} p_s²)`
  - **L23.13** (l.96): `= √(HM) Δ_r p_s`

Formalization notes:

- The sketch must render `∂_{l_h^m} p_s` in Lean.
- L23.11 ties the 2-norm of the gradient to these partial derivatives, so the rendering must be,
  or be provably equal to, the `(h, m)` entry of `gradient (provingProb Astar) l`.
- If the sketch uses two renderings, the equation between them is an **aux** gap (see the brief).

## 5. `norm_gradient_expectedReward_comp_le` (Proof sketch, l.58)

The Proof sketch says: "Specifically, ‖∇_θ p_s‖₂ is at most a constant times p_s (see Lemma 2.3)."
The Lean statement is the Setup chain rule (S.3) followed by Lemma 2.3, for `J_sparse`. The
docstring explains that `rs = 1`, `rf = 0` gives the `p_s` version.

- cite: S.3 (`norm_gradient_comp_le`) at `θ`.
- cite: Lemma 2.3 (`norm_gradient_expectedReward_le`) at `net θ`.
- **PS.1** (l.58): "‖∇_θ p_s‖₂ is at most a constant times p_s".
  - In Lean: `‖∇_θ J_sparse‖ ≤ ‖∂l/∂θ‖₂ · (√(HM) Δ_r p_s)`.
  - The step is the whole statement.

## 6. `growth` (Lemma 2.4, l.111–128)

Not steps: "Write ∇_l p_k for ∇_l p_s(l_k). Define δ = α Δ_r ∇_l p_k." (l.112). These are
definitions; use `set` or `obtain` in the sketch.

The chain (2.3)–(2.8), l.113–121. Here `l_k` is the statement's `l`, and `l_{k+1}` is
`ascentStep Astar rs rf α l`.

- **L24.1** (l.114–115): `p_{k+1} − p_k = p_s(l_k + α ∇_l J_sparse(l_k)) − p_s(l_k)`
- **L24.2** (l.116): `= p_s(l_k + δ) − p_s(l_k)`
- **L24.3** (l.117): `= (p_k + ∇_l p_kᵀ δ + ½ δᵀ (∇²_l p_s(ξ)) δ) − p_k`
  - Justification (l.123): Taylor expansion, "for some ξ between l_k and l_k + δ".
- **L24.4** (l.118): `= ∇_l p_kᵀ (α Δ_r ∇_l p_k) + ½ (α Δ_r ∇_l p_k)ᵀ (∇²_l p_s(ξ)) (α Δ_r ∇_l p_k)`
- **L24.5** (l.119): `≤ α Δ_r ‖∇_l p_k‖₂² + ½ α² Δ_r² ‖∇²_l p_s(ξ)‖₂ ‖∇_l p_k‖₂²`
  - Justification (l.123): "bounds the quadratic form by the Hessian's spectral norm", with L24.6.
- **L24.6** (l.123): `xᵀ Q x ≤ ‖Q‖₂ ‖x‖₂²`
- **L24.7** (l.120): `= α Δ_r ‖∇_l p_k‖₂² + O(α² ‖∇_l p_k‖₂²)`
  - Justification (l.123): "the bounded Hessian of the softmax".
- **L24.8** (l.121): `≤ α Δ_r (HM · p_k²) + O(α² (HM · p_k²))`
  - Justification (l.123): Lemma 2.3.

After the chain (l.123–127):

- **L24.9** (l.123): "In (2.5), for small α, the first term dominates the second,"
- **L24.10** (l.123): "so p_{k+1} ≥ p_k."
- **L24.11** (l.123–127): "Thus, 0 ≤ p_{k+1} − p_k ≤ c · p_k², c ∈ O(α · HM · Δ_r) for a
  sufficiently small α."
  - The step is the whole statement.

Formalization notes:

1. **Constants.** The Lean statement makes "sufficiently small" and `c` explicit:
   - `0 < α ≤ 1/((4H + 1) Δ_r)` and `c = 2 α H M Δ_r` (see the module docstring);
   - the `O(·)` terms of L24.7 and L24.8 become explicit terms.
2. **No Hessian in the skeleton.**
   - `provingProb_deriv2_bound` bounds the second derivative of `s ↦ p_s(l + s δ)`, which is
     `δᵀ ∇²_l p_s δ`, by `(4H + 1) ‖δ‖²`.
   - So the quadratic form `δᵀ (∇²_l p_s(ξ)) δ` of L24.3–L24.5 is rendered as that second
     derivative at some point of the segment.
   - L24.6 (`xᵀ Q x ≤ ‖Q‖₂ ‖x‖₂²`) together with the bound on `‖∇²_l p_s‖₂` is what
     `provingProb_deriv2_bound` states.
3. **Merging.** Keep one link per thesis line wherever the rendering allows. Where a thesis line
   has no Lean counterpart under this rendering, merge it into the neighbouring step and say so in
   the comment, for example `-- [L24.6 merged into L24.7: …]`.

## 7. `optReward_eq` (Proposition 2.5 proof, l.154–163)

Read the steps of Proposition 2.5 in order, P25.1 to P25.21. Steps P25.10–P25.16 are this theorem;
the others are `plateau` (item 8).

- **P25.10** (l.154–157): "Taking the supremum over l in J_sparse = Δ_r p_s + r_failure gives
  J* = Δ_r (sup_l p_s) + r_failure." This is equation (2.9).
- "For any fixed A* ∈ 𝒜*, driving each π^(h) to a point mass on v*_h (letting each l_h^{v*_h} → ∞)
  gives" (l.159–161):
  - **P25.11** (l.161): `1 ≥ p_s`
  - **P25.12** (l.161): `p_s ≥ π(A*|C)`
  - **P25.13** (l.161): `π(A*|C) = ∏_h π^(h)(v*_h|C)`
  - **P25.14** (l.159–161): `∏_h π^(h)(v*_h|C) → 1` as each `l_h^{v*_h} → ∞`
- **P25.15** (l.163): "Hence sup_l p_s = 1."
- **P25.16** (l.163, l.166): "By (2.9)", `J* = Δ_r · 1 + r_failure`, which is `r_success`.
  - The step is the whole statement.

Formalization notes:

- `J*` is `optReward`, a `⨆` over all logits.
- The sketch chooses a concrete family of logits that realizes "letting each l_h^{v*_h} → ∞".

## 8. `plateau` (Proposition 2.5, l.142–170)

Notation:

- `l_k = ascent Astar rs rf α l₀ k`, `p_k = p_s(l_k)`, and `c`, `p₀` are the statement's `let`s.
- `k̄ = 1/(2 c p₀)`.

Steps:

- cite (l.143): "By Lemma 2.4". This is `growth`, applied at `l_k`.
- **P25.1** (l.143): `p_{k+1} ≥ p_k` and `p_{k+1} − p_k ≤ c p_k²`.
- The chain, l.144–149, for every `k`:
  - **P25.2** (l.145–146): `1/p_k − 1/p_{k+1} = (p_{k+1} − p_k)/(p_k p_{k+1})`
  - **P25.3** (l.147): `≤ c p_k²/(p_k p_{k+1})`
  - **P25.4** (l.148): `= c p_k / p_{k+1}`
  - **P25.5** (l.148): `≤ c`
- **P25.6** (l.150): "Telescoping gives 1/p_0 − 1/p_k ≤ ck."
- "Hence, for all k ≤ k̄," (l.150–153):
  - **P25.7** (l.152): `1/p_k ≥ 1/p_0 − ck`
  - **P25.8** (l.152): `≥ 1/(2p_0)`
- **P25.9** (l.154): "so p_k ≤ 2p_0."
- cite: P25.16 (`optReward_eq`) and S.1 (`expectedReward_eq`).
- The chain, l.164–168, for `k ≤ k̄`:
  - **P25.17** (l.165–166): `J* − J_sparse(l_k) = (Δ_r · 1 + r_failure) − (Δ_r p_k + r_failure)`
  - **P25.18** (l.167): `= Δ_r (1 − p_k)`
  - **P25.19** (l.168): `≥ Δ_r (1 − 2p_0), ∀ k ≤ k̄`
- **P25.20** (l.170): "Hence reaching any suboptimality ε < Δ_r(1 − 2p_0) requires more than k̄
  steps." This is the second conjunct of the statement.
- **P25.21** (l.170): "With Θ(1) verifications per step, N(ε) ∈ Ω(k̄) = Ω(1/p_0)." This is the
  third conjunct, with the cumulative verification count `V`.

Formalization notes:

- The first conjunct of the statement is P25.17–P25.19.
- The divisions need `p_k > 0`. Cite `provingProb_pos`.
- The relation between `ascent … (k + 1)` and `ascentStep (ascent … k)` is the definition of the
  iterate. If the sketch needs it as an equation, that equation is an **aux** gap.

## 9. `policy_of_uniform` (Remark 2.6, l.174)

- **R26.5** (l.174): "At a uniform initialization, π(·|C) is itself uniform over 𝒜."
  - The step is the whole statement: every arm has probability `M^{−H}`.

## 10. `provingProb_of_uniform` (Remark 2.6, l.174)

- **R26.1** (l.174): "At a uniform initialization, π^(h)(m|C) = 1/M for every h and m".
  - model: this is the hypothesis `hl`.
- cite: R26.5 (`policy_of_uniform`).
- **R26.2** (l.174): "so p_0 = |𝒜*| M^{−H}". The step is the whole statement.

## 11. `plateau_uniform` (Remark 2.6, l.174)

- cite: R26.2 (`provingProb_of_uniform`) at `l₀`.
- cite: P25.20 (`plateau`, second conjunct).
- **R26.3** (l.174): "Thus, if |𝒜*| is bounded and M ≥ 2, k̄ = 1/(2cp_0) is exponential in H."
  - The Lean statement gives `k̄` explicitly as `M^H / (4 α H M Δ_r |𝒜*|)`. It does not state
    "exponential in H", and it has no premise on `|𝒜*|` or `M`. The explicit `M^H` is what the
    sentence reads off under those premises.
  - The step is the equation `1/(2 c p₀) = M^H / (4 α H M Δ_r |𝒜*|)` with `p₀ = |𝒜*| M^{−H}`.
- conclusion: the statement.

## 12. `provingProb_zero_single` (Remark 2.6, l.174)

- cite: `provingProb_of_uniform` (item 10) at `l = 0`, with `softmax_zero`, for `H = 1`.
  - Do not cite `provingProb_zero`. It is a term-mode corollary built from the skeleton's
    `provingProb_of_uniform`, so citing it would bypass the DSP version.
- **R26.4** (l.174): "A single component (H=1) with a single optimal arm (|𝒜*|=1) has p_0 = 1/M."
  The step is the whole statement.

## 13. `uniformSearch_bounds` (Remark 2.6, l.174)

- **R26.6** (l.174): "Uniform random search thus samples from the initial policy without learning,
  so its proving probability is also p_0".
  - model: the statement takes `p := provingProb Astar 0`.
- **R26.7** (l.174): "and it needs Θ(1/p_0) verifications (see Lemma 2.7)."
  - cite: `minSamples_bounds`, the explicit-constant form of Lemma 2.7, at `p := provingProb Astar 0`.
  - Its hypotheses `0 < p_0 ≤ 1` are cites of `provingProb_pos` and `provingProb_le_one`.

## 14. `minSamples_sub_isBigO` (Lemma 2.7 proof, l.186–191)

- **L27.1** (l.187): "The probability that all N independently sampled configurations fail is
  (1 − p_s)^N."
  - model: the Lean statements start from this, by the author's decision (2026-11-01).
- **L27.2** (l.187): "Hence the probability of observing at least one success is
  P_N = 1 − (1 − p_s)^N."
  - model: this is the expression inside `minSamples`.
- **L27.3** (l.187): "Solving P_N ≥ q gives N ≥ log(1 − q)/log(1 − p_s)."
- **L27.4** (l.187): "Since log(1 − p_s) = −p_s + O(p_s²),"
- **L27.5** (l.187–191): "the smallest such N is N = (−log(1 − q)/p_s)(1 + O(p_s))".
  - The docstring states the Lean form `N − (−log(1−q))/p = O(1)`.
  - The step is the whole statement.

Formalization note: "as p_s → 0" is the filter `𝓝[>] 0`, and "the smallest such N" is
`minSamples q p` (cite `minSamples_spec`).

## 15. `minSamples_isTheta` (Lemma 2.7 proof, l.192)

In the DSP file this theorem comes after `minSamples_sub_isBigO`, in thesis order.

- cite: L27.5 (`minSamples_sub_isBigO`).
- **L27.6** (l.192): "∈ Θ(1/p_s)". The step is the whole statement.

## 16. `perContext_minTotal` (Corollary 2.8 proof, l.208)

- **C28.1** (l.208): "The contexts are searched independently, so N_𝒞 = Σ_{C∈𝒞} N_C."
  The step is the whole statement.

## 17. `perContext_bounds` (Corollary 2.8 proof, l.208)

- **C28.2** (l.208): "By Lemma 2.7, N_C ∈ Θ(1/p_C) for each C."
  - cite: `minSamples_bounds` for each `C`. This is the explicit-constant form of Lemma 2.7;
    the thesis gives no proof of it.
- **C28.3** (conclusion; the statement of Corollary 2.8, l.198–205): `N_𝒞 ∈ Θ(Σ_C 1/p_C)`.
  - The proof text leaves this sum implicit.
