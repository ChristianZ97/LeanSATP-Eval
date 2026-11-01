import Sec2.RandomSearch

set_option maxHeartbeats 0

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
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hq0 hq1
    intro p hp0 hp1 N
    have ha0 : 0 < 1 - p := by linarith
    have ha1 : 1 - p < 1 := by linarith
    have hb0 : 0 < 1 - q := by linarith
    have hla : Real.log (1 - p) < 0 := by
      exact Real.log_neg ha0 ha1
    have hpow : Real.log ((1 - p) ^ N) = (N : ℝ) * Real.log (1 - p) := by
      exact Real.log_pow (1 - p) N
    have hpos : 0 < (1 - p) ^ N := pow_pos ha0 N
    have hiff : Real.log ((1 - p) ^ N) ≤ Real.log (1 - q) ↔ (1 - p) ^ N ≤ 1 - q := by
      exact Real.log_le_log_iff hpos hb0
    have hdiv : Real.log (1 - q) / Real.log (1 - p) ≤ (N : ℝ) ↔
        (N : ℝ) * Real.log (1 - p) ≤ Real.log (1 - q) := by
      exact div_le_iff_of_neg hla
    rw [hdiv, ← hpow, hiff]
    constructor <;> intro h <;> linarith
  -- [L27.4] Since log(1 − p_s) = −p_s + O(p_s²),
  have hL274 : (fun p : ℝ => Real.log (1 - p) - -p) =O[𝓝[>] 0] (fun p : ℝ => p ^ 2) := by
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * -
    have key : ∀ x : ℝ, 0 < x → Real.log x ≤ x - 1 := by
      intro x hx
      exact Real.log_le_sub_one_of_pos hx
    have hev : ∀ᶠ p in 𝓝 (0:ℝ), p < 1 / 2 := by
      exact eventually_lt_nhds (by norm_num)
    refine Asymptotics.IsBigO.mono ?_ nhdsWithin_le_nhds
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [hev] with p hp
    have h1p : (0:ℝ) < 1 - p := by linarith
    have hr : (1 - p) * (1 - p)⁻¹ = 1 := mul_inv_cancel₀ h1p.ne'
    have hr2 : (1 - p)⁻¹ ≤ 2 := by nlinarith
    have hX : 1 - (1 - p)⁻¹ + p + 2 * p ^ 2 = p ^ 2 * (2 - (1 - p)⁻¹) := by
      linear_combination (-(1 + p)) * hr
    have hXnn : 0 ≤ 1 - (1 - p)⁻¹ + p + 2 * p ^ 2 := by
      rw [hX]
      exact mul_nonneg (sq_nonneg p) (by linarith)
    have hup : Real.log (1 - p) ≤ 1 - p - 1 := key (1 - p) h1p
    have hlow : Real.log (1 - p)⁻¹ ≤ (1 - p)⁻¹ - 1 := key (1 - p)⁻¹ (inv_pos.mpr h1p)
    have hli : Real.log (1 - p)⁻¹ = -Real.log (1 - p) := Real.log_inv (1 - p)
    have hsq : 0 ≤ p ^ 2 := sq_nonneg p
    simp only [Real.norm_eq_abs]
    rw [abs_le, abs_of_nonneg hsq]
    constructor
    · linarith
    · linarith
  -- [cite: minSamples_spec] "the smallest such N" is minSamples q p (for 0 < p ≤ 1)
  have hspec : ∀ p : ℝ, 0 < p → p ≤ 1 →
      q ≤ 1 - (1 - p) ^ minSamples q p ∧ ∀ N : ℕ, q ≤ 1 - (1 - p) ^ N → minSamples q p ≤ N :=
    fun p hp0 hp1 => minSamples_spec hq0 hq1 hp0 hp1
  -- [L27.5] the smallest such N is N = (−log(1 − q)/p_s)(1 + O(p_s))   (L27.3, L27.4)
  --   Lean form: N − (−log(1 − q))/p_s = O(1) as p_s → 0⁺ (smallest N: minSamples_spec)
  have hL275 : (fun p : ℝ => (minSamples q p : ℝ) - -Real.log (1 - q) / p) =O[𝓝[>] 0]
      (fun _ : ℝ => (1 : ℝ)) := by
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hq0 hq1 hL273 hL274 hspec
    have hL : Real.log (1 - q) < 0 := Real.log_neg (by linarith) (by linarith)
    have hev : ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < p ∧ p < 1 := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with p hp0 hp1
      exact ⟨hp0, hp1⟩
    refine Asymptotics.IsBigO.of_bound (1 - Real.log (1 - q)) ?_
    filter_upwards [hev] with p hp
    obtain ⟨hp0', hp1'⟩ := hp
    have h1p : (0:ℝ) < 1 - p := by linarith
    have hl : Real.log (1 - p) < 0 := Real.log_neg h1p (by linarith)
    have hlne : Real.log (1 - p) ≠ 0 := hl.ne
    have hpne : p ≠ 0 := hp0'.ne'
    have hle1 : Real.log (1 - p) ≤ -p := by
      have h := Real.add_one_le_exp (Real.log (1 - p))
      rw [Real.exp_log h1p] at h
      linarith
    have hle2 : -Real.log (1 - p) * (1 - p) ≤ p := by
      have h := Real.add_one_le_exp (-Real.log (1 - p))
      rw [Real.exp_neg, Real.exp_log h1p] at h
      have hinv : (1 - p)⁻¹ * (1 - p) = 1 := inv_mul_cancel₀ h1p.ne'
      have h2 := mul_le_mul_of_nonneg_right h h1p.le
      rw [hinv] at h2
      linarith
    have hx : Real.log (1 - q) / Real.log (1 - p) * Real.log (1 - p) = Real.log (1 - q) := by
      exact div_mul_cancel₀ _ hlne
    have hy : -Real.log (1 - q) / p * p = -Real.log (1 - q) := by
      exact div_mul_cancel₀ _ hpne
    have hx0 : 0 ≤ Real.log (1 - q) / Real.log (1 - p) := by
      exact div_nonneg_of_nonpos hL.le hl.le
    have hA : Real.log (1 - q) / Real.log (1 - p) ≤ ((minSamples q p : ℕ) : ℝ) :=
      (hL273 p hp0' hp1' (minSamples q p)).mp (hspec p hp0' hp1'.le).1
    have hB : ((minSamples q p : ℕ) : ℝ) ≤ Real.log (1 - q) / Real.log (1 - p) + 1 := by
      have h1 : q ≤ 1 - (1 - p) ^ ⌈Real.log (1 - q) / Real.log (1 - p)⌉₊ :=
        (hL273 p hp0' hp1' _).mpr (Nat.le_ceil _)
      have h2 : minSamples q p ≤ ⌈Real.log (1 - q) / Real.log (1 - p)⌉₊ :=
        (hspec p hp0' hp1'.le).2 _ h1
      have h3 : ((minSamples q p : ℕ) : ℝ) ≤ ((⌈Real.log (1 - q) / Real.log (1 - p)⌉₊ : ℕ) : ℝ) := by
        exact Nat.cast_le.mpr h2
      have h4 : ((⌈Real.log (1 - q) / Real.log (1 - p)⌉₊ : ℕ) : ℝ) ≤
          Real.log (1 - q) / Real.log (1 - p) + 1 := by
        exact (Nat.ceil_lt_add_one hx0).le
      linarith
    have hC : Real.log (1 - q) / Real.log (1 - p) ≤ -Real.log (1 - q) / p := by
      by_contra hcon
      push_neg at hcon
      have h1 := mul_pos (sub_pos.mpr hcon) hp0'
      have h2 := mul_nonneg hx0 (by linarith : (0:ℝ) ≤ -Real.log (1 - p) - p)
      linarith
    have hD : -Real.log (1 - q) / p + Real.log (1 - q) ≤ Real.log (1 - q) / Real.log (1 - p) := by
      by_contra hcon
      push_neg at hcon
      have h1 := mul_pos (sub_pos.mpr hcon) hp0'
      have h2 := mul_nonneg hx0 (by linarith : (0:ℝ) ≤ p - -Real.log (1 - p) * (1 - p))
      have hxp : Real.log (1 - q) / Real.log (1 - p) * Real.log (1 - p) * p =
          Real.log (1 - q) * p := by
        rw [hx]
      linarith
    have hfin : |((minSamples q p : ℕ) : ℝ) - -Real.log (1 - q) / p| ≤ 1 - Real.log (1 - q) := by
      rw [abs_le]
      constructor <;> linarith
    rw [norm_one, mul_one, Real.norm_eq_abs]
    exact hfin
  exact hL275

/-- Lemma 2.7: `N ∈ Θ(1/p_s)` (as `p_s → 0⁺`). -/
theorem minSamples_isTheta {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (fun p : ℝ => (minSamples q p : ℝ)) =Θ[𝓝[>] 0] (fun p : ℝ => 1 / p) := by
  -- [cite: L27.5 (minSamples_sub_isBigO)] N = (−log(1 − q)/p_s)(1 + O(p_s))
  have hL275 := minSamples_sub_isBigO hq0 hq1
  -- [L27.6] ∈ Θ(1/p_s)   (from L27.5)
  have hL276 : (fun p : ℝ => (minSamples q p : ℝ)) =Θ[𝓝[>] 0] (fun p : ℝ => 1 / p) := by
    -- [non-satp] Configuration A inferred by satp's policy fails (`satp?` did not finish within 2400 s and was terminated).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hq0 hq1 hL275
    have hc : 0 < -Real.log (1 - q) := by
      have hlog : Real.log (1 - q) < 0 := by
        exact Real.log_neg (by linarith) (by linarith)
      linarith
    have hinv : Filter.Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] (0:ℝ)) Filter.atTop := by
      exact tendsto_inv_nhdsGT_zero
    have key : ∀ x : ℝ, -Real.log (1 - q) * x⁻¹ ≤ ‖-Real.log (1 - q) / x‖ := fun x => by
      rw [Real.norm_eq_abs, div_eq_mul_inv]; exact le_abs_self _
    have hT : Filter.Tendsto (fun x : ℝ => ‖-Real.log (1 - q) / x‖) (𝓝[>] (0:ℝ)) Filter.atTop :=
      Filter.tendsto_atTop_mono key (Filter.Tendsto.const_mul_atTop hc hinv)
    have h1 : (fun _ : ℝ => (1:ℝ)) =o[𝓝[>] (0:ℝ)] (fun p : ℝ => -Real.log (1 - q) / p) := by
      first
        | exact Asymptotics.isLittleO_one_left_iff.mpr hT
        | exact Asymptotics.isLittleO_const_left.mpr (Or.inr hT)
    have h2 : Asymptotics.IsEquivalent (𝓝[>] (0:ℝ)) (fun p : ℝ => (minSamples q p : ℝ))
        (fun p : ℝ => -Real.log (1 - q) / p) := by
      exact hL275.trans_isLittleO h1
    have h3 : (fun _ : ℝ => -Real.log (1 - q)) =Θ[𝓝[>] (0:ℝ)] (fun _ : ℝ => (1:ℝ)) := by
      exact Asymptotics.isTheta_const_const hc.ne' one_ne_zero
    have h4 : (fun p : ℝ => -Real.log (1 - q) / p) =Θ[𝓝[>] (0:ℝ)] (fun p : ℝ => 1 / p) := by
      exact h3.div (Asymptotics.isTheta_refl _ _)
    exact h2.isTheta.trans h4
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
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 7 candidate t_C; none proves it.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - hq0 hq1 hp hspec
    constructor
    · refine ⟨_, ?_, rfl⟩
      exact fun C hC => (hspec C hC).1
    · intro T hT
      simp only [Set.mem_setOf_eq] at hT
      obtain ⟨n, hn, rfl⟩ := hT
      exact sum_le_sum fun C hC => (hspec C hC).2 _ (hn C hC)
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
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hC282
    constructor
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro C hC
      rw [mul_one_div]
      exact (hC282 C hC).1
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro C hC
      rw [mul_one_div]
      exact (hC282 C hC).2
  exact hC283

end Sec2.DSP
