import Sec2.Growth

/-!
# Proposition 2.5 (Sparsity inflates verification cost) and Remark 2.6 (Implication)

Proposition 2.5 of the thesis: with `c` as in Lemma 2.4, for all `k ≤ k̄ = 1/(2 c p_0)`,
`J* − J(l_k) = Δ_r (1 − p_k) ≥ Δ_r (1 − 2 p_0)`; with `Θ(1)` verifications per step, the number
of verifications to reach `ε`-suboptimality (`ε < Δ_r (1 − 2 p_0)`) satisfies `N(ε) ∈ Ω(1/p_0)`.

Formalization:
* The step-size condition and `c` are the same as in Lemma 2.4 (`growth`):
  `0 < α ≤ 1/((4H + 1) Δ_r)` and `c = 2 α H M Δ_r`.
* `J* = sup_l J_sparse(l)`, and we prove that it equals `Δ_r · 1 + r_failure = r_success`.
* "`N(ε) ∈ Ω(1/p_0)`" is stated as: every number of steps `k` with `J* − J(l_k) ≤ ε` exceeds
  `1/(2 c p_0)`; a second version states this for the cumulative verification count `V k`
  (at least one verification per step).
-/

open Finset

namespace Sec2

variable {H M : ℕ}

/-- The `l_k` obtained from `l₀` by `k` steps of gradient ascent. -/
noncomputable def ascent (Astar : Finset (Arm H M)) (rs rf α : ℝ) (l₀ : Logits H M) (k : ℕ) :
    Logits H M :=
  (ascentStep Astar rs rf α)^[k] l₀

/-- `J*_sparse = sup_l J_sparse(l)`. -/
noncomputable def optReward (Astar : Finset (Arm H M)) (rs rf : ℝ) : ℝ :=
  ⨆ l : Logits H M, expectedReward Astar rs rf l

/-! ### `sup_l p_s = 1` (auxiliary lemmas for `optReward_eq`)

The thesis's proof: fix `A* ∈ 𝒜*` and let each `l_h^{v*_h} → ∞`;
then `π(A* ∣ C) = ∏_h π^{(h)}(v*_h ∣ C) → 1`.
Here we take `peakLogits A t`, which puts `t` at the levels chosen by `A` and `0` elsewhere; each
component gives `A h` a probability of at least `1/(1 + M e^{−t})`, a bound that tends to 1 as `t → ∞`. -/

/-- Limit: `1 + m e^{−t} → 1` as `t → ∞`. -/
private lemma tendsto_one_add_mul_exp_neg (m : ℝ) :
    Filter.Tendsto (fun t : ℝ => 1 + m * Real.exp (-t)) Filter.atTop (nhds 1) := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul m).const_add 1
  simpa using h

/-- Limit: if `f(t) → 1`, then `(1/f(t))^n → 1`. -/
private lemma tendsto_one_div_pow_of_tendsto_one (n : ℕ) (f : ℝ → ℝ)
    (hf : Filter.Tendsto f Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun t => (1 / f t) ^ n) Filter.atTop (nhds 1) := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  have h := (hf.inv₀ one_ne_zero).pow n
  simpa [one_div] using h

/-- `t ↦ (1/(1 + M e^{−t}))^H` tends to 1 as `t → ∞`. -/
private lemma tendsto_peak_lower (H M : ℕ) :
    Filter.Tendsto (fun t : ℝ => (1 / (1 + (M : ℝ) * Real.exp (-t))) ^ H) Filter.atTop
      (nhds 1) :=
  tendsto_one_div_pow_of_tendsto_one H _ (tendsto_one_add_mul_exp_neg M)

/-- Pure algebra: for `m ≥ 0`, `1/(1 + m e^{−t}) = e^t/(e^t + m)`. -/
private lemma one_div_one_add_mul_exp_neg (t m : ℝ) (hm : 0 ≤ m) :
    1 / (1 + m * Real.exp (-t)) = Real.exp t / (Real.exp t + m) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 2 round(s) and 16 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  have := Real.exp_pos t
  have h := Real.exp_neg t
  rw [h, ← inv_inj] <;> field_simp <;> ring_nf

/-- Each term of the denominator: `e^t ≤ e^t + 1` if `p` holds, and `e^0 ≤ 0 + 1` otherwise. -/
private lemma exp_ite_le (t : ℝ) (p : Prop) [Decidable p] :
    Real.exp (if p then t else 0) ≤ (if p then Real.exp t else 0) + 1 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by zify))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.add_one_le_exp]))
      (add norm 0 (by grind only [Real.exp_le_exp]))
      (add norm 0 (by grind only [Real.exp_pos]))
      (add norm 0 (by grind only [Real.le_log_iff_exp_le]))
      (add norm 0 (by grind only [Real.exp_add]))
      (add norm 0 (by grind only [Real.exp_one_rpow]))
      (add norm 0 (by grind only [le_mul_iff_one_le_left']))
      (add norm 0 (by grind only [Real.exp_le_one_iff]))
      (add norm 0 (by grind only [le_mul_iff_one_le_right']))
      (add norm 0 (by grind only [Real.exp]))
      (add norm 0 (by grind only [Real.exp_eq_exp_ℝ]))
      (add norm 0 (by grind only [Real.exp_nonneg]))
      (add norm 0 (by grind only [ProbabilityTheory.mgf_nonneg]))
      (add norm 0 (by grind only [Real.log_le_iff_le_exp]))
      (add norm 0 (by grind only [Real.one_le_exp]))
      (add norm 0 (by grind only [integral_exp]))
      (add norm 0 (by grind only [Real.log_exp]))
      (add norm 0 (by grind only [Real.exp_mul]))
      (add norm 0 (by grind only [Real.le_exp_log]))
      (add norm 0 (by grind only [Real.exp_log]))
      (add norm 0 (by grind only [rexp_neg_deriv_aux]))
      (add norm 0 (by grind only [Real.exp_sub]))
      (add norm 0 (by grind only [Real.exp_ne_zero]))
      (add norm 0 (by grind only [rexp_neg_injOn_aux]))
      (add norm 0 (by grind only [Real.exp_arsinh]))
      (add norm 0 (by grind only [zero_le_one]))
      (add norm 0 (by grind only [Real.one_le_exp_iff]))
      (add norm 0 (by grind only [Real.exp_zero]))
      (add norm 0 (by grind only [Real.rpow_def_of_pos]))
      (add unsafe 90% (by simp only [le_mul_of_one_le_right'] at *))
      (add unsafe 90% (by simp only [le_mul_of_one_le_left'] at *))
      (add unsafe 50% (by nlinarith [Behrend.lower_bound_le_one]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (bound)

/-- Sum of the termwise upper bounds: `Σ_{i : Fin n} ((e if i = a, else 0) + 1) = e + n`. -/
private lemma sum_ite_add_one (n : ℕ) (a : Fin n) (e : ℝ) :
    ∑ i : Fin n, ((if i = a then e else 0) + 1) = e + n := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [Finset.sum_add_distrib]
  simp

/-- The softmax denominator is positive: for `n > 0`, `Σ_{i : Fin n} e^{g i} > 0`. -/
private lemma sum_exp_pos (n : ℕ) (hn : 0 < n) (g : Fin n → ℝ) : 0 < ∑ i, Real.exp (g i) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  apply Finset.sum_pos
  · intros i _
    apply Real.exp_pos
  · existsi ⟨0, hn⟩
    simp

/-- Larger denominator, smaller quotient: for `e > 0` and `0 < S ≤ e + m`, `e/(e + m) ≤ e/S`. -/
private lemma div_add_le_div (e S m : ℝ) (he : 0 < e) (hS : 0 < S) (hSle : S ≤ e + m) :
    e / (e + m) ≤ e / S := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 120
      maxNormIterations := 320
      maxGoals := 512
    })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_div_right]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [div_le_div_left]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [Real.pi_le_four]))
      (add norm 0 (by grind only [div_le_div]))
      (add norm 0 (by grind only [div_le_self]))
      (add norm 0 (by grind only [Complex.mul_angle_le_norm_sub]))
      (add norm 0 (by grind only [Behrend.two_div_one_sub_two_div_e_le_eight]))
      (add norm 0 (by grind only [le_div_comm]))
      (add norm 0 (by grind only [Real.pi_div_two_le_two]))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 1 (by unfold div_le_one))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by nlinarith [Real.mul_le_sin]))
      (add safe 1 (by unfold one_le_div))
      (add safe 1 (by apply div_mul))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [SzemerediRegularity.coe_m_add_one_pos]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring)
  --   simp_all only [mul_le_mul_iff_right₀]
  --   (bound)

/-- The logits with `t` at the levels chosen by `A` and `0` elsewhere. -/
private noncomputable def peakLogits (A : Arm H M) (t : ℝ) : Logits H M :=
  WithLp.toLp 2 (fun i : Fin H × Fin M => if i.2 = A i.1 then t else 0)

/-- At `peakLogits A t`, each component gives `A h` a probability of at least `1/(1 + M e^{−t})`:
the denominator is `S = Σ_{m'} e^{l_h^{m'}} ≤ e^t + M`, so `e^t/S ≥ e^t/(e^t + M) = 1/(1 + M e^{−t})`. -/
private lemma softmax_peak_ge (hM : 0 < M) (A : Arm H M) (t : ℝ) (h : Fin H) :
    1 / (1 + (M : ℝ) * Real.exp (-t)) ≤ softmax (peakLogits A t) h (A h) := by
  -- Unfold `peakLogits`
  have hval : ∀ m' : Fin M, peakLogits A t (h, m') = if m' = A h then t else 0 := fun _ => rfl
  have hl : peakLogits A t (h, A h) = t := (hval (A h)).trans (if_pos rfl)
  -- Denominator: bound each term (`exp_ite_le`), then sum (`sum_ite_add_one`)
  have hsum : ∑ m' : Fin M, Real.exp (peakLogits A t (h, m')) ≤ Real.exp t + M := by
    simp only [hval]
    exact (Finset.sum_le_sum fun m' _ => exp_ite_le t (m' = A h)).trans_eq
      (sum_ite_add_one M (A h) (Real.exp t))
  unfold softmax
  rw [hl]
  calc 1 / (1 + (M : ℝ) * Real.exp (-t)) = Real.exp t / (Real.exp t + M) :=
        one_div_one_add_mul_exp_neg t M (Nat.cast_nonneg M)
    _ ≤ Real.exp t / ∑ m' : Fin M, Real.exp (peakLogits A t (h, m')) :=
        div_add_le_div (Real.exp t) _ M (Real.exp_pos t)
          (sum_exp_pos M hM fun m' => peakLogits A t (h, m')) hsum

/-- The lower bound is nonnegative: for `m ≥ 0`, `1/(1 + m e^{−t}) ≥ 0`. -/
private lemma one_div_one_add_mul_exp_neg_nonneg (t m : ℝ) (hm : 0 ≤ m) :
    0 ≤ 1 / (1 + m * Real.exp (-t)) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.exp_le_one_iff]))
      (add norm 0 (by grind only [zero_le_one]))
      (add norm 0 (by grind only [ProbabilityTheory.mgf_nonneg]))
      (add norm 0 (by grind only [Real.exp_nonneg]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [Real.exp_le_exp]))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [Real.one_le_exp]))
      (add norm 0 (by grind only [Real.one_le_exp_iff]))
      (add norm 0 (by grind only [Real.log_nonneg]))
      (add norm 0 (by grind only [Real.pi_nonneg]))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [le_mul_iff_one_le_right']))
      (add norm 0 (by grind only [Real.exp_pos]))
      (add norm 0 (by grind only [Real.rpow_nonneg]))
      (add norm 0 (by grind only [le_mul_iff_one_le_left']))
      (add norm 0 (by grind only [Real.le_log_iff_exp_le]))
      (add norm 0 (by grind only [div_le_one']))
      (add norm 0 (by grind only [one_le_oneLePart]))
      (add norm 0 (by grind only [Real.log_nonpos]))
      (add norm 0 (by grind only [div_le_self_iff]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [mul_nonpos_of_nonpos_of_nonneg]))
      (add norm 0 (by grind only [unitInterval.nonneg]))
      (add norm 0 (by grind only [one_le_leOnePart]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 90% (by simp only [le_mul_of_one_le_right'] at *))
      (add unsafe 90% (by simp only [le_mul_of_one_le_left'] at *))
      (add unsafe 90% (by simp only [unitInterval.le_one] at *))
      (add unsafe 50% (by nlinarith [mul_le_one]))
      (add unsafe 50% (by nlinarith [div_le_one]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [one_div, inv_nonneg]
  --   (bound)

/-- If each `f i` is `≥ x ≥ 0`, then the product satisfies `∏_{i : Fin n} f i ≥ x^n`. -/
private lemma pow_le_prod_of_le (n : ℕ) (x : ℝ) (f : Fin n → ℝ) (hx : 0 ≤ x)
    (hf : ∀ i, x ≤ f i) : x ^ n ≤ ∏ i, f i := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  induction' n with n ih
  · simp
  · rw [Fin.prod_univ_succ]
    rw [pow_succ']
    gcongr
    · exact le_trans hx (hf 0)
    · exact hf 0
    · apply ih
      exact fun i => hf _

/-- At `peakLogits A t`, `π(A ∣ C) ≥ (1/(1 + M e^{−t}))^H`. -/
private lemma policy_peak_ge (hM : 0 < M) (A : Arm H M) (t : ℝ) :
    (1 / (1 + (M : ℝ) * Real.exp (-t))) ^ H ≤ policy (peakLogits A t) A := by
  unfold policy
  exact pow_le_prod_of_le H _ _ (one_div_one_add_mul_exp_neg_nonneg t M (Nat.cast_nonneg M))
    (fun h => softmax_peak_ge hM A t h)

/-- Limit: if `f(t) → 1` and `x < 1`, then `x < f(t)` for some `t`. -/
private lemma exists_lt_of_tendsto_one (f : ℝ → ℝ) (hf : Filter.Tendsto f Filter.atTop (nhds 1))
    (x : ℝ) (hx : x < 1) : ∃ t, x < f t := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  exact ((tendsto_order.1 hf).1 x hx).exists

/-- The "≥" direction of `sup_l p_s = 1`: for every `x < 1`, some logits give `p_s > x`. -/
private lemma exists_provingProb_gt (hM : 0 < M) (Astar : Finset (Arm H M))
    (hA : Astar.Nonempty) {x : ℝ} (hx : x < 1) : ∃ l : Logits H M, x < provingProb Astar l := by
  obtain ⟨A, hAmem⟩ := hA
  obtain ⟨t, ht⟩ := exists_lt_of_tendsto_one _ (tendsto_peak_lower H M) x hx
  -- `x < π(A ∣ C) ≤ p_s`
  refine ⟨peakLogits A t, lt_of_lt_of_le ht ((policy_peak_ge hM A t).trans ?_)⟩
  exact Finset.single_le_sum (f := fun B => policy (peakLogits A t) B)
    (fun B _ => (policy_pos _ B).le) hAmem

/-- Upper bound: for `rf < rs` and `p ≤ 1`, `(rs − rf) p + rf ≤ rs`. -/
private lemma affine_le_of_le_one (rs rf p : ℝ) (hr : rf < rs) (hp : p ≤ 1) :
    (rs - rf) * p + rf ≤ rs := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [div_eq_inv_mul]))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [div_le_inv_mul_iff]))
      (add norm 0 (by grind only [inv_le_div_iff_le_mul]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [Int.sub_floor_div_mul_nonneg]))
      (add safe 1 (by simp_all only [div_eq_mul_inv]))
      (add safe 1 (by simp_all only [le_div_iff_mul_le]))
      (add safe 1 (by simp_all only [le_div_iff]))
      (add safe 1 (by simp_all only [div_le_iff]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [CircleDeg1Lift.le_translationNumber_of_add_int_le]))
      (add unsafe 50% (by nlinarith [Real.logb_le_logb]))
      (add unsafe 50% (by nlinarith [neg_div]))
      (add unsafe 50% (by nlinarith [inv_mul']))
      (add unsafe 50% (by nlinarith [CircleDeg1Lift.le_translationNumber_of_add_le]))
      (add unsafe 50% (by nlinarith [ceilDiv_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [Real.logb_le_logb_of_base_lt_one]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (nlinarith)

/-- The target probability is below 1: for `rf < rs` and `w < rs`, `(w − rf)/(rs − rf) < 1`. -/
private lemma gap_div_lt_one (rs rf w : ℝ) (hr : rf < rs) (hw : w < rs) :
    (w - rf) / (rs - rf) < 1 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add safe 0 (by nlinarith [Real.pi_div_two_pos]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [div_lt_iff']))
      (add unsafe 50% (by nlinarith [lt_div_iff']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [div_lt_one]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left]))
      (add unsafe 50% (by nlinarith [Real.aux₀]))
      (add unsafe 50% (by nlinarith [div_lt_iff_lt_mul']))
      (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt]))
      (add unsafe 50% (by nlinarith [div_lt_iff_lt_mul]))
      (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt']))
      (add unsafe 50% (by nlinarith [div_lt_self_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_right]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [div_lt_div_right]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [StrictConvexOn.slope_strict_mono_adjacent]))
      (add unsafe 50% (by nlinarith [Real.add_lt_add_iff_left]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_logb_iff]))
      (add unsafe 50% (by nlinarith [div_lt_div_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [one_lt_div]))
      (add unsafe 50% (by nlinarith [mabs_lt]))
      (add unsafe 50% (by nlinarith [Real.mul_lt_sin]))
      (add unsafe 50% (by nlinarith [Int.floor_lt]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (bound)

/-- Back to the reward: for `rf < rs` and `(w − rf)/(rs − rf) < p`, `w < (rs − rf) p + rf`. -/
private lemma lt_affine_of_div_lt (rs rf w p : ℝ) (hr : rf < rs)
    (hl : (w - rf) / (rs - rf) < p) : w < (rs - rf) * p + rf := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_lt_mul_of_lt_of_le]))
      (add norm 0 (by grind only [mul_lt_mul_of_le_of_lt]))
      (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt]))
      (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt']))
      (add unsafe 50% (by nlinarith [div_lt_iff_lt_mul']))
      (add unsafe 50% (by nlinarith [div_lt_iff_lt_mul]))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [div_lt_div_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right']))
      (add unsafe 50% (by nlinarith [lt_div_iff']))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
      (add unsafe 50% (by nlinarith [div_lt_iff']))
      (add unsafe 50% (by nlinarith [StrictConvexOn.slope_strict_mono_adjacent]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [div_lt_div_right]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [Real.add_lt_add_iff_left]))
      (add unsafe 50% (by nlinarith [div_lt_div_iff_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [mul_lt_mul₀]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_right']))
      (add unsafe 50% (by nlinarith [mul_lt_mul'']))
      (add unsafe 50% (by nlinarith [Real.arctan_add_arctan_lt_pi_div_two]))
      (add unsafe 50% (by nlinarith [zpow_lt_zpow_iff]))
      (add unsafe 50% (by nlinarith [mul_add_mul_lt_mul_add_mul]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_right']))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (ring_nf)
  --   (field_simp [*] at *)
  --   (linarith)

/-- The proof's `sup_l p_s = 1`, hence `J* = Δ_r + r_failure = r_success`. -/
theorem optReward_eq (hM : 0 < M) (Astar : Finset (Arm H M)) (hA : Astar.Nonempty)
    (rs rf : ℝ) (hr : rf < rs) :
    optReward Astar rs rf = rs := by
  unfold optReward
  apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  · -- Upper bound: `J(l) = Δ_r p_s(l) + r_failure ≤ r_success`, since `p_s ≤ 1`
    intro l
    rw [expectedReward_eq hM]
    exact affine_le_of_le_one rs rf _ hr (provingProb_le_one hM Astar l)
  · -- For each `w < r_success`, take `l` with `p_s(l) > (w − r_failure)/Δ_r`
    intro w hw
    obtain ⟨l, hl⟩ := exists_provingProb_gt hM Astar hA (gap_div_lt_one rs rf w hr hw)
    refine ⟨l, ?_⟩
    rw [expectedReward_eq hM]
    exact lt_affine_of_div_lt rs rf w _ hr hl

/-! ### Auxiliary lemmas for Proposition 2.5

The thesis's proof: by Lemma 2.4, `1/p_k − 1/p_{k+1} ≤ c`; telescoping gives `1/p_0 − 1/p_k ≤ c k`;
for `k ≤ k̄ = 1/(2 c p_0)`, `p_k ≤ 2 p_0`. -/

/-- Common denominator: for `x, y ≠ 0`, `1/x − 1/y = (y − x)/(x y)`. -/
private lemma one_div_sub_one_div_eq (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 / x - 1 / y = (y - x) / (x * y) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 120
      maxNormIterations := 320
      maxGoals := 512
      useDefaultSimpSet := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.rpow_sub]))
      (add norm 0 (by grind only [Real.rpow_sub_one]))
      (add norm 0 (by grind only [Real.rpow_sub']))
      (add norm 0 (by grind only [Real.log_mul]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [neg_div]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [Real.rpow_add_one]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [Real.log_div] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [Complex.log_ofReal_mul] at *))
      (add safe 0 (by simp only [mul_div_mul_right] at *))
      (add safe 0 (by simp only [Real.div_rpow] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [div_ne_zero] at *))
      (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (grind only [Real.rpow_sub])

/-- Dividing both sides by `x y > 0`: if `y − x ≤ c x²`, then `(y − x)/(x y) ≤ c x²/(x y)`. -/
private lemma sub_div_mul_le (x y c : ℝ) (hx : 0 < x) (hy : 0 < y) (hgrow : y - x ≤ c * x ^ 2) :
    (y - x) / (x * y) ≤ c * x ^ 2 / (x * y) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      maxGoals := 512
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [div_pow]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by grind only [Bertrand.real_main_inequality]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [tsub_le_iff_right]
  --   (bound)

/-- Cancellation: for `x, y ≠ 0`, `c x²/(x y) = c x/y`. -/
private lemma mul_sq_div_mul_eq (c x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    c * x ^ 2 / (x * y) = c * x / y := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 120
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Complex.log_ofReal_mul]))
      (add norm 0 (by grind only [Complex.cpow_add]))
      (add norm 0 (by grind only [Complex.mul_cpow_ofReal_nonneg]))
      (add norm 0 (by grind only [Complex.ofReal_mul]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [Real.log_mul]))
      (add norm 0 (by grind only [Complex.ofReal_ofNat]))
      (add norm 0 (by grind only [Complex.cpow_def_of_ne_zero]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Complex.two_pi_I_ne_zero]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [Complex.ofReal_cpow]))
      (add norm 0 (by grind only [Complex.I_ne_zero]))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [mul_div_mul_right] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
      (add safe 0 (by simp only [Complex.ofReal_div] at *))
      (add safe 0 (by simp only [mul_ne_zero] at *))
      (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))
      (add safe 0 (by simp only [div_ne_zero] at *))
      (add safe 0 (by simp only [div_left_inj'] at *))
      (add safe 0 (by simp only [add_div] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [ne_eq]
  --   (ring_nf)
  --   simp_all only [mul_eq_mul_right_iff, inv_eq_zero, or_false]
  --   (grind only [Complex.log_ofReal_mul])

/-- For `c ≥ 0`, `y > 0`, and `x ≤ y`, `c x/y ≤ c`. -/
private lemma mul_div_le_self_of_le (c x y : ℝ) (hc : 0 ≤ c) (hy : 0 < y) (hxy : x ≤ y) :
    c * x / y ≤ c := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add safe 1 (by simp_all only [div_le_iff]))
      (add safe 1 (by simp_all only [le_div_iff]))
      (add safe 1 (by simp_all only [div_le_iff']))
      (add safe 0 (by nlinarith [Real.mul_le_sin]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [Real.log_le_log_iff]))
      (add unsafe 50% (by nlinarith [Real.rpow_pos_of_pos]))
      (add unsafe 50% (by nlinarith [Real.exp_pos]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [ceilDiv_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [Real.log_rpow]))
      (add unsafe 50% (by nlinarith [Behrend.exp_neg_two_mul_le]))
      (add unsafe 50% (by nlinarith [Real.log_le_sub_one_of_pos]))
      (add unsafe 50% (by nlinarith [Real.log_le_iff_le_exp]))
      (add unsafe 50% (by nlinarith [inv_pos]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [Real.log_le_log]))
      (add unsafe 50% (by nlinarith [Behrend.lower_bound_le_one]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [inv_le]))
      (add unsafe 50% (by nlinarith [Real.le_log_iff_exp_le]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (field_simp [*] at *)
  --   (nlinarith)

/-- One-step bound (the thesis's chain): for `0 < x ≤ y`, `y − x ≤ c x²`, and `c ≥ 0`,
`1/x − 1/y = (y − x)/(x y) ≤ c x²/(x y) = c x/y ≤ c`. -/
private lemma one_div_sub_one_div_le {x y c : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hc : 0 ≤ c)
    (hgrow : y - x ≤ c * x ^ 2) : 1 / x - 1 / y ≤ c := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  calc 1 / x - 1 / y = (y - x) / (x * y) := one_div_sub_one_div_eq x y hx.ne' hy.ne'
    _ ≤ c * x ^ 2 / (x * y) := sub_div_mul_le x y c hx hy hgrow
    _ = c * x / y := mul_sq_div_mul_eq c x y hx.ne' hy.ne'
    _ ≤ c := mul_div_le_self_of_le c x y hc hy hxy

/-- Base case of the telescoping: `1/a − 1/a ≤ c · 0`. -/
private lemma telescope_zero (a c : ℝ) : 1 / a - 1 / a ≤ c * ((0 : ℕ) : ℝ) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
    })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [zero_div]))
      (add norm 0 (by grind only [div_zero]))
      (add norm 0 (by grind only [MulZeroClass]))
      (add norm 0 (by grind only [Nat.cast_zero]))
      (add norm 0 (by grind only [TrivSqZeroExt.inl_zero]))
      (add norm 0 (by grind only [harmonic_zero]))
      (add norm 0 (by grind only [EReal.coe_zero]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [FiniteField.cast_card_eq_zero]))
      (add norm 0 (by grind only [Hyperreal.coe_zero]))
      (add norm 0 (by grind only [Real.sqrt_zero]))
      (add norm 0 (by grind only [bernoulli_zero]))
      (add norm 0 (by grind only [fourier_eval_zero]))
      (add norm 0 (by grind only [Polynomial.bernoulli_zero]))
      (add norm 0 (by grind only [Int.cast_zero]))
      (add norm 0 (by grind only [Complex.logTaylor_at_zero]))
      (add norm 0 (by grind only [Rat.cast_zero]))
      (add norm 0 (by grind only [Nat.floor_zero]))
      (add norm 0 (by grind only [Quaternion.coe_zero]))
      (add norm 0 (by grind only [quadraticChar_zero]))
      (add norm 0 (by grind only [SlashInvariantForm.coe_natCast]))
      (add norm 0 (by grind only [ZNum.cast_zero]))
      (add norm 0 (by grind only [Real.sin_zero]))
      (add norm 0 (by grind only [DihedralGroup.commProb_nil]))
      (add norm 0 (by grind only [Real.Gamma_zero]))
      (add norm 0 (by grind only [LaurentPolynomial.T_zero]))
      (add norm 0 (by grind only [zero_pow]))
      (add norm 0 (by grind only [fourier_zero]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [Complex.Gamma_zero]))
      (add norm 0 (by grind only [Int.sign_zero]))
      (add unsafe 10% (by field_simp [Set.Icc.coe_zero] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring)
  --   (linarith)

/-- One telescoping step: if `1/a − 1/b ≤ c n` and `1/b − 1/d ≤ c`, then `1/a − 1/d ≤ c (n + 1)`. -/
private lemma telescope_succ (a b d c : ℝ) (n : ℕ) (ih : 1 / a - 1 / b ≤ c * n)
    (h1 : 1 / b - 1 / d ≤ c) : 1 / a - 1 / d ≤ c * ((n + 1 : ℕ) : ℝ) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
    })
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by norm_cast))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [Nat.cast_succ]))
      (add norm 0 (by grind only [Nat.cast_add]))
      (add norm 0 (by rw [Nat.cast_one]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Nat.cast_add_one]))
      (add norm 0 (by grind only [Num.cast_succ]))
      (add norm 0 (by rw [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [Nat.factorial_succ]))
      (add norm 0 (by grind only [mul_add_one]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [Nat.cast_sub]))
      (add norm 0 (by grind only [mul_lt_mul_iff_left]))
      (add norm 0 (by grind only [Num.cast_succ']))
      (add norm 0 (by rw [mul_self]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by apply div_mul))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 1 (by unfold div_le_iff))
      (add safe 0 (by simp only [div_self] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (grind only [Nat.cast_succ])

/-- Cancellation: for `c, p₀ ≠ 0`, `c · 1/(2 c p₀) = 1/(2 p₀)`, i.e., `c k̄ = 1/(2 p₀)`. -/
private lemma mul_one_div_two_mul_eq (c p0 : ℝ) (hc : c ≠ 0) (hp0 : p0 ≠ 0) :
    c * (1 / (2 * c * p0)) = 1 / (2 * p0) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 120
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [mul_inv_cancel]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Complex.cpow_add]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [Complex.log_ofReal_mul]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [inv_mul_cancel]))
      (add norm 0 (by grind only [Real.Gamma_add_one]))
      (add norm 0 (by grind only [Complex.ofReal_mul]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
      (add safe 0 (by simp only [Complex.ofReal_div] at *))
      (add safe 0 (by simp only [mul_div_mul_right] at *))
      (add safe 0 (by simp only [Complex.Gamma_one_half_eq] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [ne_eq, one_div, mul_inv_rev]
  --   (grind only [mul_assoc])

/-- For `p₀ > 0` and `x ≤ 1/(2 p₀)`, `1/(2 p₀) ≤ 1/p₀ − x`. -/
private lemma one_div_two_mul_le_sub (p0 x : ℝ) (hp0 : 0 < p0) (hx : x ≤ 1 / (2 * p0)) :
    1 / (2 * p0) ≤ 1 / p0 - x := by
  -- [satp + generative rule] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- The generator g (an Opus 5.5 subagent) supplies t_C = `2 (2 * p0)` as the arguments of lemma ℓ = `div_eq_inv_mul` in rule 31 of A.
  -- Rule type, priority, position, wrapper and ℓ are unchanged, so A′ differs from A only by t_C; arguments drawn only
  -- from names in the context do not prove the subgoal (thesis Section 5.5):
  --   A : (add norm 0 (by grind only [div_eq_inv_mul]))
  --   A′: (add norm 0 (by grind only [div_eq_inv_mul 2 (2 * p0)]))
  -- Proof body: the full A′ (A is the `satp?` output, port 5171; only the rule above and indentation changed).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
    })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_div_left]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [div_eq_inv_mul 2 (2 * p0)]))
      (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
      (add norm 0 (by grind only [one_div_le]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold div_le_div_right))
      (add safe 1 (by unfold div_le_one))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 1 (by unfold one_le_div))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [div_eq_mul_inv]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_left]))
  -- The `aesop?` "Try this" output with A′, copied verbatim (reduction: the proof aesop found):
  --   (ring)
  --   (grind only [div_eq_inv_mul 2 (2 * p0)])

/-- Taking reciprocals: if `p₀, p_k > 0` and `1/(2 p₀) ≤ 1/p_k`, then `p_k ≤ 2 p₀`. -/
private lemma le_two_mul_of_one_div_le (p0 pk : ℝ) (hp0 : 0 < p0) (hpk : 0 < pk)
    (h : 1 / (2 * p0) ≤ 1 / pk) : pk ≤ 2 * p0 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_div_right))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 100 (by simp only [mul_div_cancel₀] at *))
      (add safe 1 (by unfold div_le_one))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [one_div_le]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [zero_lt_two']))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Nat.cast_pos]))
      (add unsafe 50% (by nlinarith [zero_lt_two]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (field_simp [*] at *)
  --   (linarith)

/-- After telescoping: if `1/p_0 − 1/p_k ≤ c k` and `k ≤ k̄ = 1/(2 c p_0)` (`c > 0`), then
`1/p_k ≥ 1/p_0 − c k ≥ 1/(2 p_0)`, so `p_k ≤ 2 p_0`. -/
private lemma le_two_mul_of_telescope {p0 pk c k : ℝ} (hp0 : 0 < p0) (hpk : 0 < pk)
    (hc : 0 < c) (hk : k ≤ 1 / (2 * c * p0)) (htel : 1 / p0 - 1 / pk ≤ c * k) :
    pk ≤ 2 * p0 := by
  -- `c k ≤ c k̄ = 1/(2 p_0)`
  have hck : c * k ≤ 1 / (2 * p0) :=
    (mul_le_mul_of_nonneg_left hk hc.le).trans_eq (mul_one_div_two_mul_eq c p0 hc.ne' hp0.ne')
  -- `1/(2 p_0) ≤ 1/p_0 − c k ≤ 1/p_k`
  have h3 : 1 / (2 * p0) ≤ 1 / pk :=
    (one_div_two_mul_le_sub p0 (c * k) hp0 hck).trans (sub_le_comm.1 htel)
  exact le_two_mul_of_one_div_le p0 pk hp0 hpk h3

/-- The thesis's telescoping argument for an abstract positive sequence `P` and `c > 0`: if each
step has `P k ≤ P (k+1)` and `P (k+1) − P k ≤ c P k²`, then `P k ≤ 2 P 0` for all `k ≤ 1/(2 c P 0)`. -/
private lemma seq_plateau (P : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hpos : ∀ k, 0 < P k)
    (hstep : ∀ k, P k ≤ P (k + 1) ∧ P (k + 1) - P k ≤ c * P k ^ 2) (k : ℕ)
    (hk : (k : ℝ) ≤ 1 / (2 * c * P 0)) : P k ≤ 2 * P 0 := by
  -- Telescope `1/P n − 1/P (n+1) ≤ c` to get `1/P 0 − 1/P n ≤ c n`
  have htel : ∀ n : ℕ, 1 / P 0 - 1 / P n ≤ c * n := by
    intro n
    induction n with
    | zero => exact telescope_zero (P 0) c
    | succ n ih =>
      exact telescope_succ (P 0) (P n) (P (n + 1)) c n ih
        (one_div_sub_one_div_le (hpos n) (hstep n).1 hc.le (hstep n).2)
  exact le_two_mul_of_telescope (hpos 0) (hpos k) hc hk (htel k)

/-- `l_{k+1} = l_k + α ∇_l J_sparse(l_k)`. -/
private lemma ascent_succ (Astar : Finset (Arm H M)) (rs rf α : ℝ) (l₀ : Logits H M) (k : ℕ) :
    ascent Astar rs rf α l₀ (k + 1) = ascentStep Astar rs rf α (ascent Astar rs rf α l₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- Pure algebra: `rs − ((rs − rf) p + rf) = (rs − rf)(1 − p)`. -/
private lemma sub_affine_eq (rs rf p : ℝ) : rs - ((rs - rf) * p + rf) = (rs - rf) * (1 - p) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 100 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [div_inv_eq_mul]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [SubgroupClass.coe_div]))
      (add norm 0 (by grind only [div_mul_div_cancel']))
      (add norm 0 (by grind only [AddCommGroup.modEq_sub_iff_add_modEq]))
      (add norm 0 (by grind only [Real.Angle.coe_sub]))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [div_mul_cancel]))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by rw [Quaternion.coe_sub]))
      (add norm 0 (by grind only [ContMDiffSection.coe_sub]))
      (add norm 0 (by grind only [AddConstMapClass.map_zsmul_add]))
      (add norm 0 (by grind only [CauSeq.sub_limZero]))
      (add norm 0 (by grind only [mem_segment_translate]))
      (add norm 0 (by grind only [Complex.Gammaℝ_mul_Gammaℝ_add_one]))
      (add norm 0 (by grind only [inv_mul']))
      (add norm 0 (by grind only [mul_div_mul_left_eq_div]))
      (add norm 0 (by grind only [mul_div_mul_comm]))
      (add safe 0 (by simp only [div_mul] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add unsafe 50% (by grind only [div_eq_iff_eq_mul]))
      (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))
      (add unsafe 50% (by grind only [AddConstMapClass.map_add_zsmul]))
      (add unsafe 50% (by grind only [AddConstMapClass.map_sub_zsmul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (linarith)

/-- `J* − J(l) = Δ_r (1 − p_s(l))` (by `optReward_eq` and `expectedReward_eq`). -/
private lemma optReward_sub_expectedReward (hM : 0 < M) (Astar : Finset (Arm H M))
    (hA : Astar.Nonempty) (rs rf : ℝ) (hr : rf < rs) (l : Logits H M) :
    optReward Astar rs rf - expectedReward Astar rs rf l =
      (rs - rf) * (1 - provingProb Astar l) := by
  rw [optReward_eq hM Astar hA rs rf hr, expectedReward_eq hM Astar rs rf]
  exact sub_affine_eq rs rf _

/-- `c > 0`: for `a > 0`, `n, m > 0`, and `rf < rs`, `2 a (n m) (rs − rf) > 0`. -/
private lemma step_const_pos (a rs rf : ℝ) (n m : ℕ) (ha : 0 < a) (hn : 0 < n) (hm : 0 < m)
    (hr : rf < rs) : 0 < 2 * a * ((n : ℝ) * m) * (rs - rf) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add safe 0 (by nlinarith [Real.pi_div_two_pos]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [div_lt_iff']))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [lt_div_iff']))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [Real.aux₀]))
      (add unsafe 50% (by nlinarith [div_lt_one]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_right]))
      (add unsafe 50% (by nlinarith [one_lt_div]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [div_lt_self_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_right]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
      (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt]))
      (add unsafe 50% (by nlinarith [div_lt_iff_lt_mul']))
      (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt']))
      (add unsafe 50% (by nlinarith [div_lt_iff_lt_mul]))
      (add unsafe 50% (by nlinarith [StrictConvexOn.slope_strict_mono_adjacent]))
      (add unsafe 50% (by nlinarith [Real.mul_lt_sin]))
      (add unsafe 50% (by nlinarith [div_lt_div_right]))
      (add unsafe 50% (by nlinarith [ContDiffBump.one_lt_rOut_div_rIn]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_logb_iff]))
      (add unsafe 50% (by nlinarith [Real.pi_gt_three]))
      (add unsafe 50% (by nlinarith [inv_pos]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (bound)

/-- Lower bound on the suboptimality gap: for `d ≥ 0` and `p_k ≤ 2 p₀`, `d (1 − 2 p₀) ≤ d (1 − p_k)`. -/
private lemma gap_mul_le (d p0 pk : ℝ) (hd : 0 ≤ d) (h : pk ≤ 2 * p0) :
    d * (1 - 2 * p0) ≤ d * (1 - pk) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      maxGoals := 512
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_div]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [div_pow_le]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [div_le_one_of_le]))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [SzemerediRegularity.hundred_le_m]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (nlinarith)

/-- From step count to verification count: if `x < k` and `k ≤ v` (natural numbers), then `x < v`. -/
private lemma lt_cast_of_lt_cast_of_le (x : ℝ) (k v : ℕ) (h : x < k) (hv : k ≤ v) : x < v := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 2 round(s) and 16 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  exact h.trans_le (Nat.cast_le.2 hv)

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
  have hΔ : 0 < rs - rf := sub_pos.mpr hr
  -- `0 < H` and `0 < M` give `c > 0`
  have hc : 0 < c := step_const_pos α rs rf H M hα hH hM hr
  -- Lemma 2.4 along `l_k`, then the telescoping argument: `p_k ≤ 2 p₀` for `k ≤ k̄`
  have hbound : ∀ k : ℕ, (k : ℝ) ≤ 1 / (2 * c * p₀) →
      provingProb Astar (ascent Astar rs rf α l₀ k) ≤ 2 * p₀ := fun k hk =>
    seq_plateau (fun k => provingProb Astar (ascent Astar rs rf α l₀ k)) c hc
      (fun k => provingProb_pos Astar hA _)
      (fun k => by
        have h := growth hM Astar rs rf hr α hα hαle (ascent Astar rs rf α l₀ k)
        simp only [ascent_succ]
        exact ⟨sub_nonneg.1 h.1, h.2⟩) k hk
  -- Item 2: if `k ≤ k̄`, then `ε < Δ_r (1 − 2 p₀) ≤ Δ_r (1 − p_k) = J* − J(l_k) ≤ ε`, a contradiction
  have hsteps : ∀ ε : ℝ, ε < (rs - rf) * (1 - 2 * p₀) → ∀ k : ℕ,
      optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k) ≤ ε →
      1 / (2 * c * p₀) < k := by
    intro ε hε k hk
    by_contra hcon
    have h2 := gap_mul_le (rs - rf) p₀ _ hΔ.le (hbound k (not_lt.1 hcon))
    rw [optReward_sub_expectedReward hM Astar hA rs rf hr] at hk
    exact lt_irrefl ε (hε.trans_le (h2.trans hk))
  refine ⟨fun k hk => ⟨optReward_sub_expectedReward hM Astar hA rs rf hr _,
    gap_mul_le (rs - rf) p₀ _ hΔ.le (hbound k hk)⟩, hsteps, ?_⟩
  -- Item 3: at least one verification per step, so `k ≤ V k`
  intro V hV ε hε k hk
  exact lt_cast_of_lt_cast_of_le _ k (V k) (hsteps ε hε k hk) (hV k)

/-- The softmax when all logits are 0: `e^0 / Σ_{i : Fin n} e^0 = 1/n`. -/
private lemma exp_zero_div_sum_exp_zero (n : ℕ) :
    Real.exp 0 / ∑ _i : Fin n, Real.exp 0 = 1 / (n : ℝ) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
    })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [Real.exp_zero]))
      (add norm 0 (by grind only [Nat.cast_zero]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [div_zero]))
      (add norm 0 (by grind only [Stirling.stirlingSeq]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [MulZeroClass]))
      (add norm 0 (by grind only [Finset.prod_range_zero]))
      (add norm 0 (by grind only [Nat.factorial]))
      (add norm 0 (by grind only [Finset.prod_range_one]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [TrivSqZeroExt.inl_zero]))
      (add norm 0 (by grind only [LSeries.term_zero]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_natCast]))
      (add norm 0 (by grind only [LSeries.delta]))
      (add norm 0 (by grind only [integral_exp]))
      (add norm 0 (by grind only [Complex.logTaylor_at_zero]))
      (add norm 0 (by grind only [Finset.range_zero]))
      (add norm 0 (by grind only [ZetaAsymptotics.term_sum]))
      (add norm 0 (by grind only [Complex.exp_zero]))
      (add norm 0 (by grind only [FiniteField.cast_card_eq_zero]))
      (add norm 0 (by grind only [bernoulli_one]))
      (add norm 0 (by grind only [harmonic_succ]))
      (add norm 0 (by grind only [Real.exp_log]))
      (add safe 0 (by simp only [zero_div] at *))
      (add safe 0 (by simp only [bernoulli_zero] at *))
      (add safe 0 (by simp only [harmonic_zero] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [Complex.logTaylor_zero] at *))
      (add safe 0 (by simp only [Polynomial.bernoulli_zero] at *))
      (add safe 0 (by simp only [DihedralGroup.commProb_nil] at *))
      (add unsafe 50% (by simp_all [Nat.cast_one]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring)
  --   (bound)

/-- Remark 2.6: all-zero logits are a uniform initialization: `π^{(h)}(m ∣ C) = 1/M` for every `h` and `m`. -/
theorem softmax_zero (hM : 0 < M) (h : Fin H) (m : Fin M) :
    softmax (0 : Logits H M) h m = 1 / (M : ℝ) := by
  unfold softmax
  exact exp_zero_div_sum_exp_zero M

/-- Product of constants: `∏_{i : Fin n} 1/x = 1/x^n`. -/
private lemma prod_const_one_div (n : ℕ) (x : ℝ) : ∏ _i : Fin n, (1 / x) = 1 / x ^ n := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
    })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by simp))
      (add norm 0 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [Finset.prod_singleton]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [Finset.prod_const]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [Finset.prod_const_one]))
      (add norm 0 (by grind only [bernoulli_one]))
      (add norm 0 (by grind only [Finset.prod_empty]))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [Nat.choose_self]))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [Finset.prod_range_succ']))
      (add norm 0 (by grind only [FiniteField.sum_pow_units]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [Finset.prod_div_distrib]))
      (add norm 0 (by grind only [Finset.sum_div]))
      (add norm 0 (by grind only [LiouvilleNumber.partialSum]))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add norm 0 (by grind only [Finset.prod_range_zero]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [geom_sum₂_with_one]))
      (add norm 0 (by grind only [bernsteinPolynomial.variance]))
      (add norm 0 (by grind only [ENNReal.inner_le_Lp_mul_Lq]))
      (add norm 0 (by grind only [Finset.card_range]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [Finset.range_one] at *))
      (add safe 0 (by simp only [bernoulli_zero] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add unsafe 50% (by simp_all [Nat.cast_one]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring)
  --   (bound)

/-- Remark 2.6: at a uniform initialization (`π^{(h)}(m ∣ C) = 1/M` for every `h` and `m`), every arm
has probability `M^{−H}`, i.e., `π(·∣C)` is uniform over `𝒜`. -/
theorem policy_of_uniform (l : Logits H M) (hl : ∀ h m, softmax l h m = 1 / (M : ℝ))
    (A : Arm H M) : policy l A = 1 / (M : ℝ) ^ H := by
  unfold policy
  simp only [hl]
  exact prod_const_one_div H (M : ℝ)

/-- Sum of constants: `Σ_{i ∈ s} 1/x = |s|/x`. -/
private lemma sum_const_one_div {ι : Type*} (s : Finset ι) (x : ℝ) :
    ∑ _i ∈ s, (1 / x) = s.card / x := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [Finset.prod_const]))
      (add norm 0 (by grind only [Finset.prod_div_distrib]))
      (add norm 0 (by grind only [Finset.prod_const_one]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [Finset.prod_singleton]))
      (add norm 0 (by grind only [Nat.cast_sum]))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [Finset.sum_div]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [Finset.prod_apply]))
      (add norm 0 (by grind only [Nat.cast_prod]))
      (add norm 0 (by grind only [nsmul_eq_mul]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [sum_bernoulli]))
      (add norm 0 (by grind only [Nat.choose_self]))
      (add norm 0 (by grind only [Finset.prod_range_succ]))
      (add norm 0 (by grind only [Rat.cast_sum]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [Finpartition.coe_energy]))
      (add norm 0 (by grind only [Finset.prod_eq_one]))
      (add norm 0 (by grind only [ENNReal.inner_le_Lp_mul_Lq]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add unsafe 90% (by rw [Finset.prod]))
      (add unsafe 90% (by rw [Finset.prod_attach]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (simp)
  --   (linarith)

/-- Remark 2.6: at a uniform initialization, `p_0 = |𝒜*| M^{−H}`. -/
theorem provingProb_of_uniform (Astar : Finset (Arm H M)) (l : Logits H M)
    (hl : ∀ h m, softmax l h m = 1 / (M : ℝ)) :
    provingProb Astar l = Astar.card / (M : ℝ) ^ H := by
  unfold provingProb
  simp only [policy_of_uniform l hl]
  exact sum_const_one_div Astar ((M : ℝ) ^ H)

/-- The special case `l = 0` of `policy_of_uniform`. -/
theorem policy_zero (hM : 0 < M) (A : Arm H M) : policy (0 : Logits H M) A = 1 / (M : ℝ) ^ H :=
  policy_of_uniform 0 (softmax_zero hM) A

/-- The special case `l = 0` of `provingProb_of_uniform`: `p_s(0) = |𝒜*| M^{−H}`. -/
theorem provingProb_zero (hM : 0 < M) (Astar : Finset (Arm H M)) :
    provingProb Astar (0 : Logits H M) = Astar.card / (M : ℝ) ^ H :=
  provingProb_of_uniform Astar 0 (softmax_zero hM)

/-- Substituting `c = 2 a b d` and `p₀ = n/m` into `k̄`:
`1/(2 · (2 a b d) · (n/m)) = m/(4 a b d n)` (including the cases with `x/0 = 0`). -/
private lemma kbar_uniform_eq (a b d n m : ℝ) :
    1 / (2 * (2 * a * b * d) * (n / m)) = m / (4 * a * b * d * n) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 380
      maxNormIterations := 60
      maxGoals := 512
      useDefaultSimpSet := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [Complex.cpow_add]))
      (add norm 0 (by grind only [Complex.two_pi_I_ne_zero]))
      (add norm 0 (by grind only [Complex.ofReal_mul]))
      (add norm 0 (by grind only [div_eq_div_iff]))
      (add norm 0 (by grind only [Complex.I_ne_zero]))
      (add norm 0 (by grind only [Complex.log_ofReal_mul]))
      (add norm 0 (by grind only [div_left_inj']))
      (add norm 0 (by grind only [Complex.mul_cpow_ofReal_nonneg]))
      (add norm 0 (by grind only [Complex.ofReal_ofNat]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_mul_right] at *))
      (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
      (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))
      (add safe 0 (by simp only [Complex.ofReal_div] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [Quaternion.coe_div] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (ring_nf)
  --   (bound)

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
  intro α hα hαle l₀ hl₀ ε hε k hk
  obtain ⟨-, hsteps, -⟩ := plateau hM hH Astar hA rs rf hr α hα hαle l₀
  have hp₀ : provingProb Astar l₀ = Astar.card / (M : ℝ) ^ H :=
    provingProb_of_uniform Astar l₀ hl₀
  rw [hp₀] at hsteps
  have h := hsteps ε hε k hk
  rwa [kbar_uniform_eq] at h

/-- `|𝒜*| = 1` and `H = 1`: `(1 : ℕ)/m^1 = 1/m`. -/
private lemma cast_one_div_pow_one (m : ℕ) : ((1 : ℕ) : ℝ) / (m : ℝ) ^ 1 = 1 / (m : ℝ) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by zify))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add norm 0 (by rw [Nat.cast_one]))
      (add norm 0 (by grind only [Nat.factorial_one]))
      (add norm 0 (by grind only [ArithmeticFunction.one_apply]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_apply_one]))
      (add norm 0 (by grind only [bernoulli_one]))
      (add norm 0 (by grind only [Padic.coe_one]))
      (add norm 0 (by grind only [Nat.floor_one]))
      (add norm 0 (by grind only [bernoulli'_one]))
      (add norm 0 (by grind only [ArithmeticFunction.zeta_apply_ne]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [DihedralGroup.reciprocalFactors_one]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [ArithmeticFunction.one_apply_ne]))
      (add norm 0 (by grind only [Rat.cast_one]))
      (add norm 0 (by grind only [ArithmeticFunction.vonMangoldt_apply_one]))
      (add norm 0 (by grind only [one_ne_zero]))
      (add norm 0 (by grind only [jacobiSym.one_left]))
      (add norm 0 (by grind only [ArithmeticFunction.zeta_apply]))
      (add norm 0 (by grind only [ArithmeticFunction.const_one_eq_zeta]))
      (add norm 0 (by grind only [MulChar.map_one]))
      (add norm 0 (by grind only [ArithmeticFunction.one_one]))
      (add norm 0 (by grind only [Stirling.stirlingSeq_one]))
      (add norm 0 (by grind only [TrivSqZeroExt.inl_one]))
      (add norm 0 (by grind only [Polynomial.eval_one_cyclotomic_prime_pow]))
      (add norm 0 (by grind only [jacobiSym.one_right]))
      (add norm 0 (by rw [Quaternion.coe_one]))
      (add norm 0 (by grind only [RatFunc.denom_one]))
      (add norm 0 (by rw [LSeries.one_convolution_eq_zeta_convolution]))
      (add norm 0 (by grind only [goldenRatio]))
      (add norm 0 (by rw [FractionalIdeal.absNorm_one]))
      (add safe 0 (by simp only [bernoulli_zero] at *))
      (add safe 0 (by simp only [Complex.Gamma_one] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [Nat.cast_one, pow_one, one_div]

/-- Remark 2.6, "for H = 1, `p₀ = 1/M`", with its assumption `|𝒜*| = 1` made explicit; in general,
for `H = 1`, `p₀ = |𝒜*|/M ≥ 1/M`. -/
theorem provingProb_zero_single (hM : 0 < M) (Astar : Finset (Arm 1 M)) (h1 : Astar.card = 1) :
    provingProb Astar (0 : Logits 1 M) = 1 / (M : ℝ) := by
  rw [provingProb_zero hM, h1]
  exact cast_one_div_pow_one M

end Sec2
