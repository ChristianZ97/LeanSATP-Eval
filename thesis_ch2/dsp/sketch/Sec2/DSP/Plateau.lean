import Sec2.Plateau
import Sec2.DSP.ProveWith
import Sec2.DSP.Growth

open Finset

namespace Sec2.DSP

variable {H M : ℕ}

/-- The proof's `sup_l p_s = 1`, hence `J* = Δ_r + r_failure = r_success`. -/
theorem optReward_eq (hM : 0 < M) (Astar : Finset (Arm H M)) (hA : Astar.Nonempty)
    (rs rf : ℝ) (hr : rf < rs) :
    optReward Astar rs rf = rs := by
  -- [cite: expectedReward_eq] J_sparse = Δ_r p_s + r_failure, for every l
  have hJ : ∀ l : Logits H M, expectedReward Astar rs rf l = (rs - rf) * provingProb Astar l + rf :=
    fun l => expectedReward_eq hM Astar rs rf l
  -- [P25.11, cite: provingProb_le_one] 1 ≥ p_s
  have h11 : ∀ l : Logits H M, provingProb Astar l ≤ 1 := fun l => provingProb_le_one hM Astar l
  -- [P25.10] Taking the supremum over l in J_sparse = Δ_r p_s + r_failure gives (2.9): J* = Δ_r (sup_l p_s) + r_failure
  have h10 : optReward Astar rs rf = (rs - rf) * (⨆ l : Logits H M, provingProb Astar l) + rf := by prove_with [hJ, hM, hr, h11]
  obtain ⟨Aopt, hAopt⟩ := hA
  -- [aux] the logits that drive each π^(h) to a point mass on v*_h: l_h^{v*_h} = t → ∞, every other entry 0
  have hfam : ∃ L : ℝ → Logits H M, ∀ (t : ℝ) (h : Fin H) (m : Fin M), L t (h, m) = if m = Aopt h then t else 0 := by prove_with []
  obtain ⟨L, hL⟩ := hfam
  -- [aux, cite: policy_pos] π(A|C) > 0 for every l and every arm (used by P25.12)
  have hπ : ∀ (l : Logits H M) (A : Arm H M), 0 < policy l A := fun l A => policy_pos l A
  -- [P25.12] p_s ≥ π(A*|C)
  have h12 : ∀ l : Logits H M, policy l Aopt ≤ provingProb Astar l := by prove_with [hAopt, hπ]
  -- [P25.13] π(A*|C) = ∏_h π^(h)(v*_h|C)
  have h13 : ∀ l : Logits H M, policy l Aopt = ∏ h : Fin H, softmax l h (Aopt h) := by prove_with []
  -- [P25.14] ∏_h π^(h)(v*_h|C) → 1 as each l_h^{v*_h} → ∞
  have h14 : Filter.Tendsto (fun t : ℝ => ∏ h : Fin H, softmax (L t) h (Aopt h)) Filter.atTop (nhds 1) := by prove_with [hL]
  -- [P25.15] Hence sup_l p_s = 1
  have h15 : (⨆ l : Logits H M, provingProb Astar l) = 1 := by prove_with [h11, h12, h13, h14]
  -- [P25.16] By (2.9), J* = Δ_r · 1 + r_failure, which is r_success
  have h16 : optReward Astar rs rf = rs := by prove_with [h10, h15]
  exact h16

/-- Proposition 2.5: the step-size condition and `c` are the same as in Lemma 2.4 (`growth`). For all
`0 < α ≤ α₀ = 1 / ((4H + 1) Δ_r)` and every starting point `l₀`, take `c = 2 α H M Δ_r`. Let `l_k`
be the result of `k` steps of gradient ascent from `l₀` (`ascent`), `p_k = p_s(l_k)`, and `k̄ = 1/(2 c p₀)`:
1. for all `k ≤ k̄`, `J* − J(l_k) = Δ_r (1 − p_k) ≥ Δ_r (1 − 2 p₀)`;
2. for all `ε < Δ_r (1 − 2 p₀)`, every number of steps `k` with `J* − J(l_k) ≤ ε` exceeds `k̄`;
3. if `V k` is the cumulative verification count after `k` steps and every step uses at least one
   verification (`k ≤ V k`), then `V k > k̄` when `ε`-suboptimality is reached: this is the thesis's
   "with `Θ(1)` verifications per step, `N(ε) ∈ Ω(1/p₀)`" (the lower bound needs only "at least one").

`0 < H` excludes the degenerate case `H = 0`: there `c = 0`, and Lean's `1/0 = 0` would make `k̄` meaningless. -/
theorem plateau (hM : 0 < M) (hH : 0 < H) (Astar : Finset (Arm H M)) (hA : Astar.Nonempty)
    (rs rf : ℝ) (hr : rf < rs) :
    ∀ α : ℝ, 0 < α → α ≤ 1 / ((4 * H + 1) * (rs - rf)) → ∀ l₀ : Logits H M,
      let c := 2 * α * ((H : ℝ) * M) * (rs - rf)
      let p₀ := provingProb Astar l₀
      -- For k ≤ k̄, the suboptimality gap stays large
      (∀ k : ℕ, (k : ℝ) ≤ 1 / (2 * c * p₀) →
        optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k) =
            (rs - rf) * (1 - provingProb Astar (ascent Astar rs rf α l₀ k)) ∧
        (rs - rf) * (1 - 2 * p₀) ≤ (rs - rf) * (1 - provingProb Astar (ascent Astar rs rf α l₀ k))) ∧
      -- Every number of steps that reaches ε-suboptimality exceeds k̄ = 1/(2 c p₀)
      (∀ ε : ℝ, ε < (rs - rf) * (1 - 2 * p₀) → ∀ k : ℕ,
        optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k) ≤ ε →
        1 / (2 * c * p₀) < k) ∧
      -- Verifications: `V k` is the cumulative verification count after `k` steps. With at least one
      -- verification per step (`k ≤ V k`), the cumulative count at ε-suboptimality also exceeds k̄,
      -- i.e., the thesis's `N(ε) ∈ Ω(1/p₀)`
      (∀ V : ℕ → ℕ, (∀ k, k ≤ V k) → ∀ ε : ℝ, ε < (rs - rf) * (1 - 2 * p₀) → ∀ k : ℕ,
        optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k) ≤ ε →
        1 / (2 * c * p₀) < V k) := by
  intro α hα hαle l₀ c p₀
  -- [aux] c = 2αHMΔ_r > 0 (0 < H, 0 < M, 0 < α, Δ_r > 0); P25.5 and P25.8 need it
  have hc : 0 < c := by prove_with [hH, hM, hα, hr]
  -- [aux, cite: provingProb_pos] p_k > 0 for every k (the divisions by p_k)
  have hpos : ∀ k : ℕ, 0 < provingProb Astar (ascent Astar rs rf α l₀ k) :=
    fun k => provingProb_pos Astar hA (ascent Astar rs rf α l₀ k)
  -- [aux, cite: provingProb_pos] p₀ > 0 (the divisions by p₀)
  have hp0 : 0 < p₀ := provingProb_pos Astar hA l₀
  -- [aux] l_0 = l₀ (the iterate at 0), so p_0 is the statement's p₀
  have h0 : ascent Astar rs rf α l₀ 0 = l₀ := by prove_with []
  -- [aux] l_{k+1} = ascentStep l_k (the iterate at k + 1)
  have hsucc : ∀ k : ℕ, ascent Astar rs rf α l₀ (k + 1) = ascentStep Astar rs rf α (ascent Astar rs rf α l₀ k) := by prove_with []
  -- [P25.1, cite: growth] By Lemma 2.4 at l_k: p_{k+1} ≥ p_k and p_{k+1} − p_k ≤ c p_k²
  have h1 := fun k : ℕ => growth hM Astar rs rf hr α hα hαle (ascent Astar rs rf α l₀ k)
  have hchain : ∀ k : ℕ, 1 / provingProb Astar (ascent Astar rs rf α l₀ k) - 1 / provingProb Astar (ascent Astar rs rf α l₀ (k + 1)) ≤ c := by
    intro k
    calc 1 / provingProb Astar (ascent Astar rs rf α l₀ k) - 1 / provingProb Astar (ascent Astar rs rf α l₀ (k + 1))
        -- [P25.2] 1/p_k − 1/p_{k+1} = (p_{k+1} − p_k)/(p_k p_{k+1})
        _ = (provingProb Astar (ascent Astar rs rf α l₀ (k + 1)) - provingProb Astar (ascent Astar rs rf α l₀ k)) / (provingProb Astar (ascent Astar rs rf α l₀ k) * provingProb Astar (ascent Astar rs rf α l₀ (k + 1))) := by prove_with [hpos]
        -- [P25.3] ≤ c p_k²/(p_k p_{k+1})   (P25.1)
        _ ≤ c * provingProb Astar (ascent Astar rs rf α l₀ k) ^ 2 / (provingProb Astar (ascent Astar rs rf α l₀ k) * provingProb Astar (ascent Astar rs rf α l₀ (k + 1))) := by prove_with [h1, hsucc, hpos]
        -- [P25.4] = c p_k / p_{k+1}
        _ = c * provingProb Astar (ascent Astar rs rf α l₀ k) / provingProb Astar (ascent Astar rs rf α l₀ (k + 1)) := by prove_with [hpos]
        -- [P25.5] ≤ c   (P25.1: p_{k+1} ≥ p_k)
        _ ≤ c := by prove_with [h1, hsucc, hpos, hc]
  -- [P25.6] Telescoping gives 1/p_0 − 1/p_k ≤ ck
  have h6 : ∀ k : ℕ, 1 / p₀ - 1 / provingProb Astar (ascent Astar rs rf α l₀ k) ≤ c * k := by prove_with [hchain, h0]
  have h8 : ∀ k : ℕ, (k : ℝ) ≤ 1 / (2 * c * p₀) → 1 / provingProb Astar (ascent Astar rs rf α l₀ k) ≥ 1 / (2 * p₀) := by
    intro k hk
    calc 1 / provingProb Astar (ascent Astar rs rf α l₀ k)
        -- [P25.7] 1/p_k ≥ 1/p_0 − ck   (P25.6)
        _ ≥ 1 / p₀ - c * k := by prove_with [h6]
        -- [P25.8] ≥ 1/(2p_0)   (k ≤ k̄)
        _ ≥ 1 / (2 * p₀) := by prove_with [hk, hc, hp0]
  -- [P25.9] so p_k ≤ 2p_0, for all k ≤ k̄
  have h9 : ∀ k : ℕ, (k : ℝ) ≤ 1 / (2 * c * p₀) → provingProb Astar (ascent Astar rs rf α l₀ k) ≤ 2 * p₀ := by prove_with [h8, hpos, hp0]
  -- [cite: optReward_eq] J* = r_success = Δ_r · 1 + r_failure
  have hopt := optReward_eq hM Astar hA rs rf hr
  -- [cite: expectedReward_eq] J_sparse(l_k) = Δ_r p_k + r_failure
  have hJ := fun k : ℕ => expectedReward_eq hM Astar rs rf (ascent Astar rs rf α l₀ k)
  have hfirst : ∀ k : ℕ, (k : ℝ) ≤ 1 / (2 * c * p₀) →
      optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k) =
          (rs - rf) * (1 - provingProb Astar (ascent Astar rs rf α l₀ k)) ∧
      (rs - rf) * (1 - 2 * p₀) ≤ (rs - rf) * (1 - provingProb Astar (ascent Astar rs rf α l₀ k)) := by
    intro k hk
    have heq := calc optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k)
        -- [P25.17] J* − J_sparse(l_k) = (Δ_r · 1 + r_failure) − (Δ_r p_k + r_failure)
        _ = ((rs - rf) * 1 + rf) - ((rs - rf) * provingProb Astar (ascent Astar rs rf α l₀ k) + rf) := by prove_with [hopt, hJ]
        -- [P25.18] = Δ_r (1 − p_k)
        _ = (rs - rf) * (1 - provingProb Astar (ascent Astar rs rf α l₀ k)) := by prove_with []
    -- [P25.19] Δ_r (1 − p_k) ≥ Δ_r (1 − 2p_0), ∀ k ≤ k̄   (P25.9)
    have h19 : (rs - rf) * (1 - 2 * p₀) ≤ (rs - rf) * (1 - provingProb Astar (ascent Astar rs rf α l₀ k)) := by prove_with [h9, hk, hr]
    exact ⟨heq, h19⟩
  -- [P25.20] Hence reaching any suboptimality ε < Δ_r(1 − 2p_0) requires more than k̄ steps
  have h20 : ∀ ε : ℝ, ε < (rs - rf) * (1 - 2 * p₀) → ∀ k : ℕ, optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k) ≤ ε → 1 / (2 * c * p₀) < k := by prove_with [hfirst]
  -- [P25.21] With Θ(1) verifications per step, N(ε) ∈ Ω(k̄) = Ω(1/p_0)
  have h21 : ∀ V : ℕ → ℕ, (∀ k, k ≤ V k) → ∀ ε : ℝ, ε < (rs - rf) * (1 - 2 * p₀) → ∀ k : ℕ, optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k) ≤ ε → 1 / (2 * c * p₀) < V k := by prove_with [h20]
  exact ⟨hfirst, h20, h21⟩

/-- Remark 2.6: at a uniform initialization (`π^{(h)}(m ∣ C) = 1/M` for every `h` and `m`), every arm
has probability `M^{−H}`, i.e., `π(·∣C)` is uniform over `𝒜`. -/
theorem policy_of_uniform (l : Logits H M) (hl : ∀ h m, softmax l h m = 1 / (M : ℝ))
    (A : Arm H M) : policy l A = 1 / (M : ℝ) ^ H := by
  -- [R26.5] At a uniform initialization, π(·|C) is itself uniform over 𝒜: π(A|C) = M^{−H}
  have h5 : policy l A = 1 / (M : ℝ) ^ H := by prove_with [hl]
  exact h5

/-- Remark 2.6: at a uniform initialization, `p_0 = |𝒜*| M^{−H}`. -/
theorem provingProb_of_uniform (Astar : Finset (Arm H M)) (l : Logits H M)
    (hl : ∀ h m, softmax l h m = 1 / (M : ℝ)) :
    provingProb Astar l = Astar.card / (M : ℝ) ^ H := by
  -- [cite: policy_of_uniform] π(A|C) = M^{−H} for every arm
  have h5 : ∀ A : Arm H M, policy l A = 1 / (M : ℝ) ^ H := fun A => policy_of_uniform l hl A
  -- [R26.2] so p_0 = |𝒜*| M^{−H}
  have h2 : provingProb Astar l = Astar.card / (M : ℝ) ^ H := by prove_with [h5]
  exact h2

/-- Remark 2.6 (Implication): at a uniform initialization (`π^{(h)}(m ∣ C) = 1/M` for every `h` and
`m`, e.g., `l₀ = 0`), `p₀ = |𝒜*| M^{−H}`, so `k̄ = 1/(2 c p₀) = M^H / (2 c |𝒜*|)`
(`c = 2α·HM·Δ_r`; the step-size condition is the same as in `growth` and `plateau`), and every
number of steps that reaches ε-suboptimality exceeds it.
The thesis's remark that `k̄` is exponential in `H` holds when `p₀` decreases exponentially in `H`,
e.g., `M ≥ 2` and bounded `|𝒜*|`; this statement makes that assumption explicit. Without it the
growth can fail: `𝒜* = {A : A 0 = 1}` has `M^{H−1}` arms, `p₀ = 1/M`, and `k̄ = 1/(4α·H·Δ_r)`
decreases with `H`. -/
theorem plateau_uniform (hM : 0 < M) (hH : 0 < H) (Astar : Finset (Arm H M)) (hA : Astar.Nonempty)
    (rs rf : ℝ) (hr : rf < rs) :
    ∀ α : ℝ, 0 < α → α ≤ 1 / ((4 * H + 1) * (rs - rf)) →
      ∀ l₀ : Logits H M, (∀ h m, softmax l₀ h m = 1 / (M : ℝ)) →
      ∀ ε : ℝ, ε < (rs - rf) * (1 - 2 * (Astar.card / (M : ℝ) ^ H)) → ∀ k : ℕ,
        optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k) ≤ ε →
        (M : ℝ) ^ H / (4 * α * ((H : ℝ) * M) * (rs - rf) * Astar.card) < k := by
  intro α hα hαle l₀ hl ε hε k hk
  -- [cite: provingProb_of_uniform] at l₀: p₀ = |𝒜*| M^{−H}
  have hp0 := provingProb_of_uniform Astar l₀ hl
  -- [cite: plateau, second conjunct] every number of steps that reaches ε-suboptimality exceeds k̄ = 1/(2cp₀)
  have h20 := (plateau hM hH Astar hA rs rf hr α hα hαle l₀).2.1
  -- [R26.3] k̄ = 1/(2cp_0) = M^H/(4αHMΔ_r|𝒜*|), with p_0 = |𝒜*| M^{−H}
  have h3 : 1 / (2 * (2 * α * ((H : ℝ) * M) * (rs - rf)) * provingProb Astar l₀) = (M : ℝ) ^ H / (4 * α * ((H : ℝ) * M) * (rs - rf) * Astar.card) := by prove_with [hp0]
  -- [conclusion]
  prove_with [h20, hp0, h3, hε, hk]

/-- Remark 2.6, "for H = 1, `p₀ = 1/M`", with its assumption `|𝒜*| = 1` made explicit; in general,
for `H = 1`, `p₀ = |𝒜*|/M ≥ 1/M`. -/
theorem provingProb_zero_single (hM : 0 < M) (Astar : Finset (Arm 1 M)) (h1 : Astar.card = 1) :
    provingProb Astar (0 : Logits 1 M) = 1 / (M : ℝ) := by
  -- [cite: provingProb_of_uniform] at l = 0 (uniform by softmax_zero), H = 1: p_0 = |𝒜*| M^{−1}
  have hp := provingProb_of_uniform Astar (0 : Logits 1 M) (softmax_zero hM)
  -- [R26.4] A single component (H=1) with a single optimal arm (|𝒜*|=1) has p_0 = 1/M
  have h4 : provingProb Astar (0 : Logits 1 M) = 1 / (M : ℝ) := by prove_with [hp, h1]
  exact h4

end Sec2.DSP
