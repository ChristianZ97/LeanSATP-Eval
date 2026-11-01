import Sec2.RandomSearch
import Sec2.DSP.ProveWith

open Filter Topology Asymptotics Finset

namespace Sec2.DSP

/-- Last sentence of Remark 2.6: at a uniform initialization, `π(·∣C)` is uniform over `𝒜`
(`policy_zero`), and uniform random search is exactly sampling from the initial policy, with proving
probability `p_0 = |𝒜*|/M^H` (`provingProb_zero`). By Lemma 2.7, it needs `Θ(1/p_0)` samples, with
constants independent of `H`, `M`, and `𝒜*`. -/
theorem uniformSearch_bounds {H M : ℕ} (hM : 0 < M) (Astar : Finset (Arm H M))
    (hA : Astar.Nonempty) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q / provingProb Astar 0 ≤ minSamples q (provingProb Astar 0) ∧
      (minSamples q (provingProb Astar 0) : ℝ) ≤ (-Real.log (1 - q) + 1) / provingProb Astar 0 := by
  -- [R26.6, model] Uniform random search thus samples from the initial policy without learning,
  --   so its proving probability is also p₀: the statement takes p := p_s(0).

  -- [R26.7, cite: minSamples_bounds] and it needs Θ(1/p₀) verifications (see Lemma 2.7)
  --   at p := p_s(0); its hypotheses 0 < p₀ ≤ 1 are provingProb_pos and provingProb_le_one
  exact minSamples_bounds hq0 hq1 (provingProb_pos Astar hA 0) (provingProb_le_one hM Astar 0)

/-- The more precise conclusion `N = −log(1−q)/p · (1 + O(p))` in the proof of Lemma 2.7, which is
equivalent to `N − (−log(1−q))/p = O(1)` (as `p → 0⁺`). -/
theorem minSamples_sub_isBigO {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (fun p : ℝ => (minSamples q p : ℝ) - -Real.log (1 - q) / p) =O[𝓝[>] 0]
      (fun _ : ℝ => (1 : ℝ)) := by
  -- [L27.1, L27.2, model] All N samples fail with probability (1 − p_s)^N, so
  --   P_N = 1 − (1 − p_s)^N; this is the expression inside minSamples.

  -- [L27.3] Solving P_N ≥ q gives N ≥ log(1 − q)/log(1 − p_s).
  have hL273 : ∀ p : ℝ, 0 < p → p < 1 → ∀ N : ℕ,
      (q ≤ 1 - (1 - p) ^ N ↔ Real.log (1 - q) / Real.log (1 - p) ≤ (N : ℝ)) := by
    prove_with [hq0, hq1]
  -- [L27.4] Since log(1 − p_s) = −p_s + O(p_s²),
  have hL274 : (fun p : ℝ => Real.log (1 - p) - -p) =O[𝓝[>] 0] (fun p : ℝ => p ^ 2) := by
    prove_with []
  -- [cite: minSamples_spec] "the smallest such N" is minSamples q p (for 0 < p ≤ 1)
  have hspec : ∀ p : ℝ, 0 < p → p ≤ 1 →
      q ≤ 1 - (1 - p) ^ minSamples q p ∧ ∀ N : ℕ, q ≤ 1 - (1 - p) ^ N → minSamples q p ≤ N :=
    fun p hp0 hp1 => minSamples_spec hq0 hq1 hp0 hp1
  -- [L27.5] the smallest such N is N = (−log(1 − q)/p_s)(1 + O(p_s))   (L27.3, L27.4)
  --   Lean form: N − (−log(1 − q))/p_s = O(1) as p_s → 0⁺ (smallest N: minSamples_spec)
  have hL275 : (fun p : ℝ => (minSamples q p : ℝ) - -Real.log (1 - q) / p) =O[𝓝[>] 0]
      (fun _ : ℝ => (1 : ℝ)) := by
    prove_with [hq0, hq1, hL273, hL274, hspec]
  exact hL275

/-- Lemma 2.7: `N ∈ Θ(1/p_s)` (as `p_s → 0⁺`). -/
theorem minSamples_isTheta {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (fun p : ℝ => (minSamples q p : ℝ)) =Θ[𝓝[>] 0] (fun p : ℝ => 1 / p) := by
  -- [cite: L27.5 (minSamples_sub_isBigO)] N = (−log(1 − q)/p_s)(1 + O(p_s))
  have hL275 := minSamples_sub_isBigO hq0 hq1
  -- [L27.6] ∈ Θ(1/p_s)   (from L27.5)
  have hL276 : (fun p : ℝ => (minSamples q p : ℝ)) =Θ[𝓝[>] 0] (fun p : ℝ => 1 / p) := by
    prove_with [hq0, hq1, hL275]
  exact hL276

/-- The first step of the proof of Corollary 2.8, "the contexts are searched independently, so
`N_𝒞 = Σ_C N_C`": each context `C` is allotted `n_C` samples; for every context to reach, on its
own, "probability of at least one success ≥ `q`", the smallest total number of verifications is
exactly `Σ_C N_C` (`N_C = minSamples q (p C)`; one sample counts as one verification). -/
theorem perContext_minTotal {ι : Type*} (s : Finset ι) (p : ι → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hp : ∀ C ∈ s, 0 < p C ∧ p C ≤ 1) :
    IsLeast {T : ℕ | ∃ n : ι → ℕ, (∀ C ∈ s, q ≤ 1 - (1 - p C) ^ n C) ∧ T = ∑ C ∈ s, n C}
      (∑ C ∈ s, minSamples q (p C)) := by
  -- [aux, cite: minSamples_spec] for each C ∈ s, N_C = minSamples q (p C) reaches P_N ≥ q and
  --   is the smallest such N (used by C28.1)
  have hspec : ∀ C ∈ s, q ≤ 1 - (1 - p C) ^ minSamples q (p C) ∧
      ∀ N : ℕ, q ≤ 1 - (1 - p C) ^ N → minSamples q (p C) ≤ N :=
    fun C hC => minSamples_spec hq0 hq1 (hp C hC).1 (hp C hC).2
  -- [C28.1] The contexts are searched independently, so N_𝒞 = Σ_{C∈𝒞} N_C.
  have hC281 :
      IsLeast {T : ℕ | ∃ n : ι → ℕ, (∀ C ∈ s, q ≤ 1 - (1 - p C) ^ n C) ∧ T = ∑ C ∈ s, n C}
        (∑ C ∈ s, minSamples q (p C)) := by
    prove_with [hq0, hq1, hp, hspec]
  exact hC281

/-- Corollary 2.8: finitely many contexts (`s`), each with proving probability `p_C ∈ (0, 1]`.
"Probability at least `q`" is a requirement on each context separately (the reading used in the
thesis's proof), so `N_𝒞 = Σ_C N_C` with `N_C = minSamples q (p C)` (see `perContext_minTotal`). The
constants depend only on `q`, not on the number of contexts or on the individual `p_C`:
`q · Σ_C 1/p_C ≤ N_𝒞 ≤ (−log(1−q) + 1) · Σ_C 1/p_C`, that is, `N_𝒞 ∈ Θ(Σ_C 1/p_C)`. -/
theorem perContext_bounds {ι : Type*} (s : Finset ι) (p : ι → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hp : ∀ C ∈ s, 0 < p C ∧ p C ≤ 1) :
    q * ∑ C ∈ s, 1 / p C ≤ ∑ C ∈ s, (minSamples q (p C) : ℝ) ∧
      ∑ C ∈ s, (minSamples q (p C) : ℝ) ≤ (-Real.log (1 - q) + 1) * ∑ C ∈ s, 1 / p C := by
  -- [C28.2, cite: minSamples_bounds] By Lemma 2.7, N_C ∈ Θ(1/p_C) for each C.
  --   for each C ∈ s; its hypotheses 0 < p_C ≤ 1 are hp C
  have hC282 : ∀ C ∈ s, q / p C ≤ minSamples q (p C) ∧
      (minSamples q (p C) : ℝ) ≤ (-Real.log (1 - q) + 1) / p C :=
    fun C hC => minSamples_bounds hq0 hq1 (hp C hC).1 (hp C hC).2
  -- [C28.3] N_𝒞 ∈ Θ(Σ_{C∈𝒞} 1/p_C)   (from C28.2 for each C)
  --   conclusion: the statement of Corollary 2.8 (l.198–205); the proof leaves the sum implicit
  have hC283 : q * ∑ C ∈ s, 1 / p C ≤ ∑ C ∈ s, (minSamples q (p C) : ℝ) ∧
      ∑ C ∈ s, (minSamples q (p C) : ℝ) ≤ (-Real.log (1 - q) + 1) * ∑ C ∈ s, 1 / p C := by
    prove_with [hC282]
  exact hC283

end Sec2.DSP
