# Thesis steps and gaps

Every step of the draft (`draft/steps.md`), the gap the sketch made of it, and the stage that
closed the gap. Line numbers refer to Chapter 2 of the thesis. Gap numbers are the order of the
gaps in `../project/Sec2/DSP/*.lean`.

| Step | Thesis | Step in the thesis | Lean theorem | Gap | Closed by |
|---|---|---|---|---|---|
| S.1 | l.67 | "With C fixed, J_sparse = Δ_r p_s + r_failure." | `expectedReward_eq` | 1 | Opus 5.5 |
| S.2 | l.67 | "Hence ∇_l J_sparse = Δ_r ∇_l p_s." | `gradient_expectedReward` | 2 | bfsaesop |
| S.3 | l.67–71 | "By the chain rule, ‖∇_θ J_sparse‖₂ ≤ ‖∂l/∂θ‖₂ · ‖∇_l J_sparse‖₂." | `norm_gradient_comp_le` | 3 | Opus 5.5 |
| L23.1 | l.81 | "Each entry l_h^m enters only π^(h) in π(A\|C) = ∏_{h'} π^(h')(v_{h'}\|C)." | `norm_gradient_expectedReward_le` | 4 | Opus 5.5 |
| L23.2 | l.83–84 | `\|∂_{l_h^m} p_s\| = \|Σ_{A∈𝒜*} ∂_{l_h^m} ∏_{h'} π^(h')(v_{h'}\|C)\|` | `norm_gradient_expectedReward_le` | 7 | Opus 5.5 |
| L23.3 | l.85 | `= \|Σ_{A∈𝒜*} (∏_{h'≠h} π^(h')(v_{h'}\|C)) · ∂_{l_h^m} π^(h)(v_h\|C)\|` | `norm_gradient_expectedReward_le` | 8 | Opus 5.5 |
| L23.4 | l.86 | `= \|Σ_{A∈𝒜*} (∏_{h'≠h} π^(h')(v_{h'}\|C) · π^(h)(v_h\|C)) · (1(v_h = m) − π^(h)(m\|C))\|` | `norm_gradient_expectedReward_le` | 9 | Opus 5.5 |
| L23.5 | l.86, the underbrace | `∏_{h'≠h} π^(h')(v_{h'}\|C) · π^(h)(v_h\|C) = π(A\|C)` | `norm_gradient_expectedReward_le` | 5 | bfsaesop |
| L23.6 | l.87 | `= \|Σ_{A∈𝒜*} π(A\|C) · (1(v_h = m) − π^(h)(m\|C))\|` | `norm_gradient_expectedReward_le` | 10 | satp |
| L23.7 | l.88 | `≤ Σ_{A∈𝒜*} π(A\|C)` | `norm_gradient_expectedReward_le` | 11 | Opus 5.5 |
| L23.8 | l.90 | `\|1(·) − π^(h)(m\|C)\| ≤ 1` | `norm_gradient_expectedReward_le` | 6 | Opus 5.5 |
| L23.9 | l.88 | `Σ_{A∈𝒜*} π(A\|C) = p_s` | `norm_gradient_expectedReward_le` | 12 | satp |
| L23.10 | l.92–93 | `‖∇_l J_sparse‖₂ = Δ_r ‖∇_l p_s‖₂` | `norm_gradient_expectedReward_le` | 14 | bfsaesop |
| L23.11 | l.94 | `= Δ_r √(Σ_{h,m} (∂_{l_h^m} p_s)²)` | `norm_gradient_expectedReward_le` | 15 | Opus 5.5 |
| L23.12 | l.95 | `≤ Δ_r √(Σ_{h,m} p_s²)` | `norm_gradient_expectedReward_le` | 16 | Opus 5.5 |
| L23.13 | l.96 | `= √(HM) Δ_r p_s` | `norm_gradient_expectedReward_le` | 17 | satp |
| PS.1 | l.58 | "‖∇_θ p_s‖₂ is at most a constant times p_s" | `norm_gradient_expectedReward_comp_le` | 18 | Opus 5.5 (see note 2) |
| L24.1 | l.114–115 | `p_{k+1} − p_k = p_s(l_k + α ∇_l J_sparse(l_k)) − p_s(l_k)` | `growth` | 19 | satp |
| L24.2 | l.116 | `= p_s(l_k + δ) − p_s(l_k)` | `growth` | 20 | Opus 5.5 |
| L24.3 | l.117 | `= (p_k + ∇_l p_kᵀ δ + ½ δᵀ (∇²_l p_s(ξ)) δ) − p_k` | `growth` | 22 | Opus 5.5 |
| L24.4 | l.118 | `= ∇_l p_kᵀ (α Δ_r ∇_l p_k) + ½ (α Δ_r ∇_l p_k)ᵀ (∇²_l p_s(ξ)) (α Δ_r ∇_l p_k)` | `growth` | 23 | satp |
| L24.5 | l.119 | `≤ α Δ_r ‖∇_l p_k‖₂² + ½ α² Δ_r² ‖∇²_l p_s(ξ)‖₂ ‖∇_l p_k‖₂²` | `growth` | 24 (merged into L24.7) | Opus 5.5 |
| L24.6 | l.123 | `xᵀ Q x ≤ ‖Q‖₂ ‖x‖₂²` | `growth` | 24 (merged into L24.7) | Opus 5.5 |
| L24.7 | l.120 | `= α Δ_r ‖∇_l p_k‖₂² + O(α² ‖∇_l p_k‖₂²)` | `growth` | 24 | Opus 5.5 |
| L24.8 | l.121 | `≤ α Δ_r (HM · p_k²) + O(α² (HM · p_k²))` | `growth` | 25 | Opus 5.5 |
| L24.9 | l.123 | "In (2.5), for small α, the first term dominates the second," | `growth` | 26 | Opus 5.5 |
| L24.10 | l.123 | "so p_{k+1} ≥ p_k." | `growth` | 27 | bfsaesop |
| L24.11 | l.123–127 | "Thus, 0 ≤ p_{k+1} − p_k ≤ c · p_k², c ∈ O(α · HM · Δ_r) for a sufficiently small α." | `growth` | 28 | Opus 5.5 |
| P25.10 | l.154–157 | "Taking the supremum over l in J_sparse = Δ_r p_s + r_failure gives J* = Δ_r (sup_l p_s) + r_failure." | `optReward_eq` | 29 | Opus 5.5 |
| P25.11 | l.161 | `1 ≥ p_s` | `optReward_eq` | — | cite of `provingProb_le_one` |
| P25.12 | l.161 | `p_s ≥ π(A*\|C)` | `optReward_eq` | 31 | bfsaesop |
| P25.13 | l.161 | `π(A*\|C) = ∏_h π^(h)(v*_h\|C)` | `optReward_eq` | 32 | satp |
| P25.14 | l.159–161 | `∏_h π^(h)(v*_h\|C) → 1` as each `l_h^{v*_h} → ∞` | `optReward_eq` | 33 | Opus 5.5 |
| P25.15 | l.163 | "Hence sup_l p_s = 1." | `optReward_eq` | 34 | Opus 5.5 |
| P25.16 | l.163, l.166 | "By (2.9)", `J* = Δ_r · 1 + r_failure`, which is `r_success` | `optReward_eq` | 35 | satp |
| P25.1 | l.143 | `p_{k+1} ≥ p_k` and `p_{k+1} − p_k ≤ c p_k²` | `plateau` | — | cite of `growth` |
| P25.2 | l.145–146 | `1/p_k − 1/p_{k+1} = (p_{k+1} − p_k)/(p_k p_{k+1})` | `plateau` | 39 | satp |
| P25.3 | l.147 | `≤ c p_k²/(p_k p_{k+1})` | `plateau` | 40 | bfsaesop |
| P25.4 | l.148 | `= c p_k / p_{k+1}` | `plateau` | 41 | satp |
| P25.5 | l.148 | `≤ c` | `plateau` | 42 | Opus 5.5 |
| P25.6 | l.150 | "Telescoping gives 1/p_0 − 1/p_k ≤ ck." | `plateau` | 43 | bfsaesop |
| P25.7 | l.152 | `1/p_k ≥ 1/p_0 − ck` | `plateau` | 44 | satp |
| P25.8 | l.152 | `≥ 1/(2p_0)` | `plateau` | 45 | bfsaesop |
| P25.9 | l.154 | "so p_k ≤ 2p_0." | `plateau` | 46 | satp |
| P25.17 | l.165–166 | `J* − J_sparse(l_k) = (Δ_r · 1 + r_failure) − (Δ_r p_k + r_failure)` | `plateau` | 47 | satp |
| P25.18 | l.167 | `= Δ_r (1 − p_k)` | `plateau` | 48 | satp |
| P25.19 | l.168 | `≥ Δ_r (1 − 2p_0), ∀ k ≤ k̄` | `plateau` | 49 | satp |
| P25.20 | l.170 | "Hence reaching any suboptimality ε < Δ_r(1 − 2p_0) requires more than k̄ steps." | `plateau` | 50 | bfsaesop |
| P25.21 | l.170 | "With Θ(1) verifications per step, N(ε) ∈ Ω(k̄) = Ω(1/p_0)." | `plateau` | 51 | bfsaesop |
| R26.5 | l.174 | "At a uniform initialization, π(·\|C) is itself uniform over 𝒜." | `policy_of_uniform` | 52 | bfsaesop |
| R26.1 | l.174 | "At a uniform initialization, π^(h)(m\|C) = 1/M for every h and m" | `provingProb_of_uniform` | — | model: built into the Lean statements |
| R26.2 | l.174 | "so p_0 = \|𝒜*\| M^{−H}" | `provingProb_of_uniform` | 53 | bfsaesop |
| R26.3 | l.174 | "Thus, if \|𝒜*\| is bounded and M ≥ 2, k̄ = 1/(2cp_0) is exponential in H." | `plateau_uniform` | 54 | bfsaesop |
| R26.4 | l.174 | "A single component (H=1) with a single optimal arm (\|𝒜*\|=1) has p_0 = 1/M." | `provingProb_zero_single` | 56 | bfsaesop |
| R26.6 | l.174 | "Uniform random search thus samples from the initial policy without learning, so its proving probability is also p_0" | `uniformSearch_bounds` | — | model: built into the Lean statements |
| R26.7 | l.174 | "and it needs Θ(1/p_0) verifications (see Lemma 2.7)." | `uniformSearch_bounds` | — | cite of `minSamples_bounds` |
| L27.1 | l.187 | "The probability that all N independently sampled configurations fail is (1 − p_s)^N." | `minSamples_sub_isBigO` | — | model: built into the Lean statements |
| L27.2 | l.187 | "Hence the probability of observing at least one success is P_N = 1 − (1 − p_s)^N." | `minSamples_sub_isBigO` | — | model: built into the Lean statements |
| L27.3 | l.187 | "Solving P_N ≥ q gives N ≥ log(1 − q)/log(1 − p_s)." | `minSamples_sub_isBigO` | 57 | Opus 5.5 |
| L27.4 | l.187 | "Since log(1 − p_s) = −p_s + O(p_s²)," | `minSamples_sub_isBigO` | 58 | Opus 5.5 |
| L27.5 | l.187–191 | "the smallest such N is N = (−log(1 − q)/p_s)(1 + O(p_s))" | `minSamples_sub_isBigO` | 59 | Opus 5.5 |
| L27.6 | l.192 | "∈ Θ(1/p_s)" | `minSamples_isTheta` | 60 | Opus 5.5 |
| C28.1 | l.208 | "The contexts are searched independently, so N_𝒞 = Σ_{C∈𝒞} N_C." | `perContext_minTotal` | 61 | bfsaesop |
| C28.2 | l.208 | "By Lemma 2.7, N_C ∈ Θ(1/p_C) for each C." | `perContext_bounds` | — | cite of `minSamples_bounds` |
| C28.3 | conclusion; the statement of Corollary 2.8, l.198–205 | `N_𝒞 ∈ Θ(Σ_C 1/p_C)` | `perContext_bounds` | 62 | Opus 5.5 |

## Gaps that are not thesis steps

| Gap | Lean theorem | Kind | What it states | Closed by |
|---|---|---|---|---|
| 13 | `norm_gradient_expectedReward_le` | aux | the (h, m) entry of ∇_l p_s equals the rendering of ∂_{l_h^m} p_s used in L23.2–L23.9 | Opus 5.5 |
| 21 | `growth` | aux | p_s is C² in the logits (Taylor expansion, L24.3) | Opus 5.5 |
| 30 | `optReward_eq` | aux | a family of logits with l_h^{v*_h} = t and every other entry 0 (P25.14) | Opus 5.5 |
| 36 | `plateau` | aux | c = 2αHMΔ_r > 0 | satp |
| 37 | `plateau` | aux | l_0 = l₀ (the iterate at 0) | satp |
| 38 | `plateau` | aux | l_{k+1} = ascentStep l_k (the iterate at k + 1) | bfsaesop |
| 55 | `plateau_uniform` | conclusion | plateau_uniform: the statement from P25.20 and R26.3 | satp |

## Notes

1. L24.5 and L24.6 have no Lean counterpart: the statements have no Hessian object, and
   `provingProb_deriv2_bound` bounds the second derivative along a line. As `draft/steps.md`
   allows, the sketch merged them into the gap of L24.7.
2. Gap 18: `bfsaesop` found a proof, but its "Try this" output does not replay
   (`No goals to be solved`). The gap is credited to the next stage, Opus 5.5.
3. The order of the file differs from the thesis in one place: the citation of P25.11 comes
   before P25.10, which uses it.
