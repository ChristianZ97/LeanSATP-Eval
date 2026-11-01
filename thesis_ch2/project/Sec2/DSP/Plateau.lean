import Sec2.Plateau
import Sec2.DSP.Growth

set_option maxHeartbeats 0

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
  have h10 : optReward Astar rs rf = (rs - rf) * (⨆ l : Logits H M, provingProb Astar l) + rf := by
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hJ hM hr h11
    have hc : 0 < rs - rf := sub_pos.mpr hr
    haveI : Nonempty (Logits H M) := ⟨0⟩
    have hbdd : BddAbove (Set.range fun l : Logits H M => provingProb Astar l) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨l, rfl⟩
      exact h11 l
    have hbddE : BddAbove (Set.range fun l : Logits H M => expectedReward Astar rs rf l) := by
      refine ⟨rs, ?_⟩
      rintro _ ⟨l, rfl⟩
      have h1 := hJ l
      have h2 := mul_le_mul_of_nonneg_left (h11 l) hc.le
      show expectedReward Astar rs rf l ≤ rs
      linarith
    unfold optReward
    apply le_antisymm
    · apply ciSup_le
      intro l
      have h1 := hJ l
      have h3 : provingProb Astar l ≤ ⨆ l' : Logits H M, provingProb Astar l' := le_ciSup hbdd l
      have h4 := mul_le_mul_of_nonneg_left h3 hc.le
      linarith
    · have key : (⨆ l : Logits H M, provingProb Astar l) ≤
          ((⨆ l : Logits H M, expectedReward Astar rs rf l) - rf) / (rs - rf) := by
        apply ciSup_le
        intro l
        rw [le_div_iff₀ hc]
        have h1 := hJ l
        have h3 : expectedReward Astar rs rf l ≤ ⨆ l' : Logits H M, expectedReward Astar rs rf l' :=
          le_ciSup hbddE l
        linarith
      rw [le_div_iff₀ hc] at key
      linarith
  obtain ⟨Aopt, hAopt⟩ := hA
  -- [aux] the logits that drive each π^(h) to a point mass on v*_h: l_h^{v*_h} = t → ∞, every other entry 0
  have hfam : ∃ L : ℝ → Logits H M, ∀ (t : ℝ) (h : Fin H) (m : Fin M), L t (h, m) = if m = Aopt h then t else 0 := by
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * -
    exact ⟨fun t => WithLp.toLp (p := 2) (fun x : Fin H × Fin M => if x.2 = Aopt x.1 then t else 0), fun _ _ _ => rfl⟩
  obtain ⟨L, hL⟩ := hfam
  -- [aux, cite: policy_pos] π(A|C) > 0 for every l and every arm (used by P25.12)
  have hπ : ∀ (l : Logits H M) (A : Arm H M), 0 < policy l A := fun l A => policy_pos l A
  -- [P25.12] p_s ≥ π(A*|C)
  have h12 : ∀ l : Logits H M, policy l Aopt ≤ provingProb Astar l := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - hAopt hπ
    unfold policy
    intro l
    unfold provingProb
    apply le_trans
    apply le_of_eq
    on_goal 2 => apply Finset.single_le_sum
    rfl
    · exact fun A hA => (hπ l A).le
    · assumption
  -- [P25.13] π(A*|C) = ∏_h π^(h)(v*_h|C)
  have h13 : ∀ l : Logits H M, policy l Aopt = ∏ h : Fin H, softmax l h (Aopt h) := by
    -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
    -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
    clear * -
    aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        enableUnfold := false
      })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by interval_cases))
        (add safe 0 (by ext))
        (add safe 0 (by split))
        (add safe 100 (by norm_num [*] at *))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [PFunctor.M.Approx.sMk]))
        (add norm 0 (by grind only [Computable.ofNat]))
        (add norm 0 (by grind only [Computable.comp]))
        (add norm 0 (by grind only [Computable.cond]))
        (add norm 0 (by grind only [Computable.of_eq]))
        (add norm 0 (by grind only [Computable]))
        (add norm 0 (by grind only [Computable.pair]))
        (add norm 0 (by grind only [Tree.unitRecOn]))
        (add norm 0 (by grind only [Computable.option_bind]))
        (add norm 0 (by grind only [Computation.Corec.f]))
        (add norm 0 (by grind only [Computability.Γ']))
        (add norm 0 (by grind only [PFunctor.Approx.sCorec]))
        (add norm 0 (by grind only [Computable.nat_casesOn]))
        (add norm 0 (by grind only [Nat.Partrec.Code.ofNatCode]))
        (add norm 0 (by grind only [PFunctor.M.dest]))
        (add norm 0 (by grind only [Poly.map_apply]))
        (add norm 0 (by grind only [Computable.option_map]))
        (add norm 0 (by grind only [Computation.corec]))
        (add norm 0 (by grind only [PFunctor.M.corec]))
        (add norm 0 (by grind only [System.Platform.numBits]))
        (add norm 0 (by grind only [Computable.fst]))
        (add norm 0 (by grind only [Stream'.iterate]))
        (add norm 0 (by grind only [Turing.TM2ComputableInTime.toTM2Computable]))
        (add norm 0 (by grind only [List.range]))
        (add norm 0 (by grind only [Stream'.corec]))
        (add norm 0 (by grind only [QPF.Fix.rec]))
        (add norm 0 (by grind only [Computable.eqv]))
        (add norm 0 (by grind only [MvPFunctor.M.corecContents]))
        (add norm 0 (by grind only [Quiver.Path.comp]))
        (add norm 0 (by grind only [Computable.snd]))
        (add norm 0 (by grind only [Computable.nat_strong_rec]))
        (add norm 0 (by grind only [MvQPF.Fix.rec]))
    -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
    --   intro l
    --   (bound)
  -- [P25.14] ∏_h π^(h)(v*_h|C) → 1 as each l_h^{v*_h} → ∞
  have h14 : Filter.Tendsto (fun t : ℝ => ∏ h : Fin H, softmax (L t) h (Aopt h)) Filter.atTop (nhds 1) := by
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hL
    have key : ∀ h : Fin H, Filter.Tendsto (fun t : ℝ => softmax (L t) h (Aopt h)) Filter.atTop (nhds 1) := by
      intro h
      have hMpos : (1:ℝ) ≤ M := by
        have h1 : 1 ≤ M := by
          have := (Aopt h).isLt
          omega
        exact_mod_cast h1
      have hform : ∀ t : ℝ, softmax (L t) h (Aopt h) = 1 - ((M:ℝ) - 1) / (Real.exp t - 1 + (M:ℝ)) := by
        intro t
        have hexp : ∀ m' : Fin M, Real.exp ((L t) (h, m')) = (if m' = Aopt h then Real.exp t - 1 else 0) + 1 := by
          intro m'
          rw [hL]
          split_ifs <;> simp
        have hsum : ∑ m' : Fin M, Real.exp ((L t) (h, m')) = Real.exp t - 1 + (M:ℝ) := by
          rw [Finset.sum_congr rfl (fun m' _ => hexp m'), Finset.sum_add_distrib]
          simp
        have hpos : 0 < Real.exp t - 1 + (M:ℝ) := by
          have := Real.exp_pos t
          linarith
        unfold softmax
        rw [hsum, hL, if_pos rfl, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
        ring
      have hD : Filter.Tendsto (fun t : ℝ => Real.exp t - 1 + (M:ℝ)) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_mono (fun t => by linarith) Real.tendsto_exp_atTop
      have h0 : Filter.Tendsto (fun t : ℝ => 1 - ((M:ℝ) - 1) / (Real.exp t - 1 + (M:ℝ))) Filter.atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hD)
      rw [sub_zero] at h0
      exact h0.congr (fun t => (hform t).symm)
    have hprod := tendsto_finset_prod (Finset.univ : Finset (Fin H)) (fun h _ => key h)
    rw [Finset.prod_const_one] at hprod
    exact hprod
  -- [P25.15] Hence sup_l p_s = 1
  have h15 : (⨆ l : Logits H M, provingProb Astar l) = 1 := by
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 7 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - h11 h12 h13 h14
    have hne : Nonempty (Logits H M) := ⟨0⟩
    have hb : BddAbove (Set.range fun l : Logits H M => provingProb Astar l) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨l, rfl⟩
      exact h11 l
    refine le_antisymm (ciSup_le h11) (le_of_tendsto' h14 fun t => ?_)
    exact (h13 (L t)).symm.le.trans ((h12 (L t)).trans (le_ciSup hb (L t)))
  -- [P25.16] By (2.9), J* = Δ_r · 1 + r_failure, which is r_success
  have h16 : optReward Astar rs rf = rs := by
    -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
    -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
    clear * - h10 h15
    aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
      })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 1 (by push_neg))
        (add norm 100 (by gcongr))
        (add norm 0 (by bound))
        (add norm 1 (by simp))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by interval_cases))
        (add safe 0 (by ext))
        (add safe 0 (by split))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 10% (by exfalso))
        (add norm 0 (by grind only [iSup_pos]))
        (add norm 0 (by grind only [ciSup_pos]))
        (add norm 0 (by grind only [iSup_subtype']))
        (add norm 0 (by grind only [Submonoid.iSup_induction]))
        (add norm 0 (by grind only [IsMaxOn.iSup_eq]))
        (add norm 0 (by grind only [iSup_eq_iSup_subseq_of_monotone]))
        (add norm 0 (by grind only [ciSup_const]))
        (add norm 0 (by grind only [Submodule.mul_iSup]))
        (add norm 0 (by grind only [Ideal.Filtration.iSup_N]))
        (add norm 0 (by grind only [Subgroup.iSup_induction]))
        (add norm 0 (by grind only [Submodule.iSup_mul]))
        (add norm 0 (by grind only [map_iSup₂]))
        (add norm 0 (by grind only [ciSup_eq_ite]))
        (add norm 0 (by grind only [iSup_comm]))
        (add norm 0 (by grind only [IntermediateField.exists_finset_of_mem_iSup]))
        (add norm 0 (by grind only [NNReal.coe_iSup]))
        (add norm 0 (by grind only [Cardinal.add_ciSup]))
        (add norm 0 (by grind only [iSup_le_iSup_of_partialSups_le_partialSups]))
        (add norm 0 (by grind only [HomogeneousIdeal.toIdeal_iSup₂]))
        (add norm 0 (by grind only [HomogeneousIdeal.toIdeal_iSup]))
        (add norm 0 (by grind only [ciSup_div]))
        (add norm 0 (by grind only [Monotone.map_iSup_of_continuousAt]))
        (add norm 0 (by grind only [biSup_mono]))
        (add norm 0 (by grind only [NNReal.mul_iSup]))
        (add norm 0 (by grind only [iSup_const]))
        (add norm 0 (by grind only [mul_ciSup]))
        (add norm 0 (by grind only [IntermediateField.exists_finset_of_mem_supr'']))
        (add norm 0 (by grind only [iSup_comp_le]))
        (add norm 0 (by grind only [Submodule.fg_iSup]))
        (add norm 0 (by grind only [Cardinal.mul_ciSup]))
        (add norm 0 (by grind only [Real.mul_iSup_of_nonneg]))
        (add norm 0 (by grind only [Filter.map_iSup]))
    -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
    --   simp_all only [mul_one, sub_add_cancel]
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
  have hc : 0 < c := by
    -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
    -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
    clear * - hH hM hα hr
    aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        maxGoals := 512
        enableSimp := false
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
        (add safe 100 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [sq_pos_of_pos]))
        (add safe 0 (by nlinarith [Real.pi_pos]))
        (add unsafe 50% (by nlinarith [mul_le_mul_right]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
        (add unsafe 50% (by nlinarith [mul_le_mul_left]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
        (add unsafe 50% (by nlinarith [le_div_iff]))
        (add unsafe 50% (by nlinarith [div_lt_iff]))
        (add unsafe 50% (by nlinarith [le_div_iff']))
        (add unsafe 50% (by nlinarith [div_le_iff]))
        (add unsafe 50% (by nlinarith [zero_lt_two']))
        (add unsafe 50% (by nlinarith [div_le_iff']))
        (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
        (add unsafe 50% (by nlinarith [one_lt_div']))
        (add unsafe 50% (by nlinarith [lt_div_iff]))
        (add unsafe 50% (by nlinarith [div_lt_iff']))
        (add unsafe 50% (by nlinarith [zero_lt_two]))
        (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
        (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
        (add unsafe 50% (by nlinarith [lt_div_iff']))
        (add unsafe 50% (by nlinarith [Real.pi_div_two_pos]))
        (add unsafe 50% (by nlinarith [Real.aux₀]))
        (add unsafe 50% (by nlinarith [div_le_div_right]))
        (add unsafe 50% (by nlinarith [div_le_one]))
        (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
        (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_right]))
        (add unsafe 50% (by nlinarith [Real.pi_gt_three]))
        (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt]))
        (add unsafe 50% (by nlinarith [one_half_pos]))
        (add unsafe 50% (by nlinarith [div_lt_one]))
        (add unsafe 50% (by nlinarith [inv_pos]))
        (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
    -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
    --   (bound)
  -- [aux, cite: provingProb_pos] p_k > 0 for every k (the divisions by p_k)
  have hpos : ∀ k : ℕ, 0 < provingProb Astar (ascent Astar rs rf α l₀ k) :=
    fun k => provingProb_pos Astar hA (ascent Astar rs rf α l₀ k)
  -- [aux, cite: provingProb_pos] p₀ > 0 (the divisions by p₀)
  have hp0 : 0 < p₀ := provingProb_pos Astar hA l₀
  -- [aux] l_0 = l₀ (the iterate at 0), so p_0 is the statement's p₀
  have h0 : ascent Astar rs rf α l₀ 0 = l₀ := by
    -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
    -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
    clear * -
    aesop (config := {
        maxRuleApplications := 40
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
      })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 100 (by exfalso))
        (add norm 1 (by field_simp [*] at *))
        (add norm 1 (by norm_num [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Ordnode.alter]))
        (add norm 0 (by grind only [Nat.any]))
        (add norm 0 (by grind only [Batteries.RBNode.alter]))
        (add norm 0 (by grind only [Substring.any]))
        (add norm 0 (by grind only [Batteries.RBNode.all]))
        (add norm 0 (by grind only [Cardinal.aleph'_zero]))
        (add norm 0 (by grind only [Part.assert_neg]))
        (add norm 0 (by grind only [List.all_cons]))
        (add norm 0 (by grind only [String.any]))
        (add norm 0 (by grind only [ContinuousLinearMap.apply_apply']))
        (add norm 0 (by grind only [List.all_eq_not_any_not]))
        (add norm 0 (by grind only [Substring.all]))
        (add norm 0 (by grind only [String.all]))
        (add norm 0 (by grind only [Nat.all]))
        (add norm 0 (by grind only [Matrix.adjugate_pow]))
        (add norm 0 (by grind only [Batteries.AssocList.any]))
        (add norm 0 (by grind only [Stream'.WSeq.any]))
        (add norm 0 (by grind only [Real.arsinh_zero]))
        (add norm 0 (by grind only [Cardinal.aleph'_lt]))
        (add norm 0 (by grind only [Cardinal.aleph'_alephIdx]))
        (add norm 0 (by grind only [ack_succ_zero]))
        (add norm 0 (by grind only [Part.assert]))
        (add norm 0 (by grind only [Batteries.RBNode.All.append]))
        (add norm 0 (by grind only [List.any_cons]))
        (add norm 0 (by grind only [Cardinal.aleph'_succ]))
        (add norm 0 (by grind only [List.any]))
        (add norm 0 (by grind only [Batteries.AssocList.all]))
        (add norm 0 (by grind only [Real.arcsin_zero]))
        (add norm 0 (by grind only [String.any_eq]))
        (add norm 0 (by grind only [ChainComplex.augment]))
        (add norm 0 (by grind only [String.anyAux_of_valid]))
        (add norm 0 (by grind only [Batteries.RBNode.Any_def]))
    -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
    --   (bound)
  -- [aux] l_{k+1} = ascentStep l_k (the iterate at k + 1)
  have hsucc : ∀ k : ℕ, ascent Astar rs rf α l₀ (k + 1) = ascentStep Astar rs rf α (ascent Astar rs rf α l₀ k) := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * -
    intro k
    unfold ascent
    simp [Function.iterate_succ_apply']
  -- [P25.1, cite: growth] By Lemma 2.4 at l_k: p_{k+1} ≥ p_k and p_{k+1} − p_k ≤ c p_k²
  have h1 := fun k : ℕ => growth hM Astar rs rf hr α hα hαle (ascent Astar rs rf α l₀ k)
  have hchain : ∀ k : ℕ, 1 / provingProb Astar (ascent Astar rs rf α l₀ k) - 1 / provingProb Astar (ascent Astar rs rf α l₀ (k + 1)) ≤ c := by
    intro k
    calc 1 / provingProb Astar (ascent Astar rs rf α l₀ k) - 1 / provingProb Astar (ascent Astar rs rf α l₀ (k + 1))
        -- [P25.2] 1/p_k − 1/p_{k+1} = (p_{k+1} − p_k)/(p_k p_{k+1})
        _ = (provingProb Astar (ascent Astar rs rf α l₀ (k + 1)) - provingProb Astar (ascent Astar rs rf α l₀ k)) / (provingProb Astar (ascent Astar rs rf α l₀ k) * provingProb Astar (ascent Astar rs rf α l₀ (k + 1))) := by
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * - hpos
          aesop (config := {
              maxRuleApplications := 100
              maxRuleApplicationDepth := 600
              maxNormIterations := 320
              maxGoals := 512
              enableSimp := false
            })
              (add norm 100 (by norm_cast))
              (add norm 0 (by linarith))
              (add norm 0 (by nlinarith))
              (add norm 0 (by omega))
              (add norm 1 (by push_neg))
              (add norm 0 (by bound))
              (add norm 0 (by ring_nf))
              (add norm 100 (by simp_all))
              (add norm 1 (by field_simp [*] at *))
              (add norm 1 (by norm_num [*] at *))
              (add safe 100 (by ring))
              (add safe 100 (by field_simp))
              (add safe 100 (by norm_num))
              (add safe 100 (by positivity))
              (add safe 100 (by interval_cases))
              (add safe 0 (by ext))
              (add safe 0 (by split))
              (add safe 0 (by exfalso))
              (add safe 1 (by ring_nf at *))
              (add safe 100 (by rfl))
              (add safe 100 (by decide))
              (add safe 0 (by push_cast))
              (add safe 100 (by assumption_mod_cast))
              (add norm 0 (by grind only [mul_div_right_comm]))
              (add norm 0 (by grind only [mul_div_assoc']))
              (add norm 0 (by grind only [tsub_div]))
              (add norm 0 (by grind only [div_mul_eq_mul_div]))
              (add norm 0 (by grind only [mul_div_cancel_left]))
              (add norm 0 (by grind only [mul_div_left_comm]))
              (add norm 0 (by grind only [mul_div_cancel_right]))
              (add norm 0 (by grind only [div_add_div_same]))
              (add norm 0 (by grind only [one_div]))
              (add norm 0 (by grind only [mul_one_div]))
              (add norm 0 (by grind only [half_add_self]))
              (add norm 0 (by grind only [NNReal.div_le_iff]))
              (add norm 0 (by grind only [div_div_eq_mul_div]))
              (add norm 0 (by grind only [two_ne_zero']))
              (add norm 0 (by grind only [div_add']))
              (add safe 0 (by simp only [mul_div] at *))
              (add safe 0 (by simp only [div_self] at *))
              (add safe 0 (by simp only [mul_div_assoc] at *))
              (add safe 0 (by simp only [div_div] at *))
              (add safe 0 (by simp only [add_div] at *))
              (add safe 0 (by simp only [div_mul] at *))
              (add safe 0 (by simp only [sub_div] at *))
              (add safe 0 (by simp only [eq_div_iff] at *))
              (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
              (add safe 0 (by simp only [mul_div_mul_left] at *))
              (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
              (add safe 0 (by simp only [div_eq_iff] at *))
              (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
              (add safe 0 (by simp only [div_mul_cancel₀] at *))
              (add safe 0 (by simp only [div_right_comm] at *))
              (add safe 0 (by simp only [mul_div_cancel₀] at *))
              (add safe 0 (by simp only [mul_div_mul_right] at *))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   (ring_nf)
          --   (grind only [mul_div_right_comm])
        -- [P25.3] ≤ c p_k²/(p_k p_{k+1})   (P25.1)
        _ ≤ c * provingProb Astar (ascent Astar rs rf α l₀ k) ^ 2 / (provingProb Astar (ascent Astar rs rf α l₀ k) * provingProb Astar (ascent Astar rs rf α l₀ (k + 1))) := by
          -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
          -- (indentation adjusted only).
          clear * - h1 hsucc hpos
          gcongr
          · exact mul_nonneg (hpos k).le (hpos (k + 1)).le
          · specialize h1 k
            simp_rw [hsucc]
            exact h1.2
        -- [P25.4] = c p_k / p_{k+1}
        _ = c * provingProb Astar (ascent Astar rs rf α l₀ k) / provingProb Astar (ascent Astar rs rf α l₀ (k + 1)) := by
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * - hpos
          aesop (config := {
              maxRuleApplications := 100
              maxRuleApplicationDepth := 380
              maxNormIterations := 320
              maxGoals := 512
              enableUnfold := false
            })
              (add norm 100 (by norm_cast))
              (add norm 0 (by linarith))
              (add norm 0 (by nlinarith))
              (add norm 1 (by push_neg))
              (add norm 0 (by bound))
              (add norm 0 (by ring_nf))
              (add norm 1 (by field_simp [*] at *))
              (add norm 1 (by norm_num [*] at *))
              (add safe 100 (by field_simp))
              (add safe 100 (by norm_num))
              (add safe 100 (by positivity))
              (add safe 100 (by omega))
              (add safe 100 (by interval_cases))
              (add safe 0 (by ext))
              (add safe 0 (by split))
              (add safe 0 (by exfalso))
              (add safe 100 (by norm_cast at *))
              (add safe 100 (by rfl))
              (add safe 100 (by decide))
              (add safe 0 (by push_cast))
              (add safe 100 (by assumption_mod_cast))
              (add unsafe 50% (by ring_nf at *))
              (add norm 0 (by grind only [mul_div_assoc']))
              (add norm 0 (by grind only [div_mul_eq_mul_div]))
              (add norm 0 (by grind only [mul_div_left_comm]))
              (add norm 0 (by grind only [mul_right_comm]))
              (add norm 0 (by grind only [tsub_div]))
              (add norm 0 (by grind only [mul_comm]))
              (add norm 0 (by grind only [Finpartition.coe_energy]))
              (add norm 0 (by grind only [div_div_eq_mul_div]))
              (add safe 0 (by simp only [mul_div_assoc] at *))
              (add safe 0 (by simp only [mul_div] at *))
              (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
              (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
              (add safe 0 (by simp only [eq_div_iff] at *))
              (add safe 0 (by simp only [div_div] at *))
              (add safe 0 (by simp only [div_eq_iff] at *))
              (add safe 0 (by simp only [mul_div_mul_left] at *))
              (add safe 0 (by simp only [div_self] at *))
              (add safe 0 (by simp only [div_mul_cancel₀] at *))
              (add safe 0 (by simp only [mul_div_cancel₀] at *))
              (add safe 0 (by simp only [add_div] at *))
              (add safe 0 (by simp only [mul_div_right_comm] at *))
              (add safe 0 (by simp only [mul_div_mul_right] at *))
              (add safe 0 (by simp only [div_mul] at *))
              (add safe 0 (by simp only [sub_div] at *))
              (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
              (add safe 0 (by simp only [two_ne_zero'] at *))
              (add safe 0 (by simp only [div_right_comm] at *))
              (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
              (add safe 0 (by simp only [div_add'] at *))
              (add safe 0 (by simp only [div_left_inj'] at *))
              (add safe 0 (by simp only [div_eq_div_iff] at *))
              (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   simp_all only [c]
          --   (ring_nf)
          --   (ring_nf)
          --   (grind only [mul_div_assoc'])
        -- [P25.5] ≤ c   (P25.1: p_{k+1} ≥ p_k)
        _ ≤ c := by
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * - h1 hsucc hpos hc
          have hk := (h1 k).1
          rw [← hsucc k] at hk
          have hp1 := hpos (k + 1)
          have key := mul_nonneg hc.le hk
          rw [div_le_iff₀ hp1]
          nlinarith
  -- [P25.6] Telescoping gives 1/p_0 − 1/p_k ≤ ck
  have h6 : ∀ k : ℕ, 1 / p₀ - 1 / provingProb Astar (ascent Astar rs rf α l₀ k) ≤ c * k := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - hchain h0
    intro k
    induction' k with k ih
    · simp [h0]
      rfl
    · rw [Nat.cast_succ]
      linarith only [ih, hchain k]
  have h8 : ∀ k : ℕ, (k : ℝ) ≤ 1 / (2 * c * p₀) → 1 / provingProb Astar (ascent Astar rs rf α l₀ k) ≥ 1 / (2 * p₀) := by
    intro k hk
    calc 1 / provingProb Astar (ascent Astar rs rf α l₀ k)
        -- [P25.7] 1/p_k ≥ 1/p_0 − ck   (P25.6)
        _ ≥ 1 / p₀ - c * k := by
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * - h6
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
              (add norm 1 (by field_simp [*] at *))
              (add safe 100 (by ring))
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
              (add norm 0 (by grind only [le_div_iff_mul_le]))
              (add norm 0 (by grind only [le_div_iff]))
              (add norm 0 (by grind only [div_le_iff_le_mul]))
              (add norm 0 (by grind only [div_le_iff]))
              (add norm 0 (by grind only [div_le_iff_le_mul']))
              (add norm 0 (by grind only [le_div_iff_mul_le']))
              (add norm 0 (by grind only [mul_le_mul_left]))
              (add norm 0 (by grind only [div_le_iff']))
              (add norm 0 (by grind only [mul_le_mul_iff_left]))
              (add norm 0 (by grind only [mul_le_mul_iff_right]))
              (add norm 0 (by grind only [div_le_div_right]))
              (add norm 0 (by grind only [div_le_div_iff_left]))
              (add norm 0 (by grind only [div_mul]))
              (add norm 0 (by grind only [div_le_div_iff]))
              (add norm 0 (by grind only [div_eq_mul_inv]))
              (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
              (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
              (add norm 0 (by grind only [mul_comm]))
              (add norm 0 (by grind only [Real.pi_le_four]))
              (add norm 0 (by grind only [mul_div_cancel_left]))
              (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
              (add norm 0 (by grind only [mul_div_cancel_right]))
              (add norm 0 (by grind only [CircleDeg1Lift.floor_sub_le_translationNumber]))
              (add norm 0 (by grind only [div_le_div_left]))
              (add norm 0 (by grind only [mul_le_mul_right']))
              (add safe 0 (by simp only [div_div] at *))
              (add safe 0 (by simp only [mul_div_assoc] at *))
              (add safe 0 (by simp only [mul_div] at *))
              (add unsafe 50% (by nlinarith [mul_le_mul_right]))
              (add unsafe 50% (by nlinarith [le_div_iff']))
              (add unsafe 50% (by nlinarith [div_le_one]))
              (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_left]))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   simp_all only [one_div, tsub_le_iff_right, ge_iff_le, p₀, c]
          --   (ring_nf)
          --   (ring_nf)
          --   (grind only [le_div_iff_mul_le])
        -- [P25.8] ≥ 1/(2p_0)   (k ≤ k̄)
        _ ≥ 1 / (2 * p₀) := by
          -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: no lemma rule of A that the search ran can be edited.
          -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
          -- (indentation adjusted only).
          clear * - hk hc hp0
          field_simp at hk ⊢
          linarith
  -- [P25.9] so p_k ≤ 2p_0, for all k ≤ k̄
  have h9 : ∀ k : ℕ, (k : ℝ) ≤ 1 / (2 * c * p₀) → provingProb Astar (ascent Astar rs rf α l₀ k) ≤ 2 * p₀ := by
    -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
    -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
    clear * - h8 hpos hp0
    aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        maxGoals := 16
      })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
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
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
        (add norm 0 (by grind only [mul_le_mul]))
        (add norm 0 (by grind only [one_le_two]))
        (add norm 0 (by grind only [pow_le_pow_left]))
        (add norm 0 (by grind only [mul_le_mul_left']))
        (add norm 0 (by rw [mul_le_mul_iff_left]))
        (add norm 0 (by grind only [mul_le_mul_right']))
        (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
        (add norm 0 (by grind only [mul_le_mul']))
        (add norm 0 (by grind only [mul_le_mul_iff_right]))
        (add norm 0 (by grind only [pow_le_pow_left']))
        (add norm 0 (by grind only [zero_le_two]))
        (add norm 0 (by grind only [Nat.cast_le]))
        (add norm 0 (by grind only [Real.BohrMollerup.f_add_nat_ge]))
        (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
        (add safe 1 (by unfold le_div_iff))
        (add safe 1 (by unfold div_le_iff))
        (add safe 1 (by unfold div_le_iff'))
        (add unsafe 50% (by nlinarith [mul_le_mul_left]))
        (add unsafe 10% (by grind only [le_trans]))
        (add unsafe 50% (by nlinarith [mul_le_mul_right]))
        (add unsafe 50% (by nlinarith [Real.pi_le_four]))
        (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
        (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
        (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
        (add unsafe 50% (by nlinarith [le_of_mul_le_mul_left]))
        (add unsafe 50% (by nlinarith [le_div_iff']))
        (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
        (add unsafe 50% (by nlinarith [le_mul_iff_one_le_right']))
        (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₄]))
        (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
        (add unsafe 50% (by nlinarith [le_mul_iff_one_le_left']))
    -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
    --   intro k a
    --   simp_all only [one_div, mul_inv_rev, ge_iff_le, p₀, c]
    --   (ring_nf)
    --   (field_simp [*] at *)
    --   simp_all only [one_div, mul_inv_rev]
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
        _ = ((rs - rf) * 1 + rf) - ((rs - rf) * provingProb Astar (ascent Astar rs rf α l₀ k) + rf) := by
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * - hopt hJ
          aesop (config := {
              maxRuleApplications := 100
              maxNormIterations := 320
              maxGoals := 512
            })
              (add norm 100 (by norm_cast))
              (add norm 0 (by linarith))
              (add norm 0 (by nlinarith))
              (add norm 0 (by positivity))
              (add norm 0 (by omega))
              (add norm 1 (by push_neg))
              (add norm 0 (by gcongr))
              (add norm 0 (by bound))
              (add norm 0 (by ring_nf))
              (add norm 1 (by ext))
              (add norm 1 (by simp))
              (add norm 1 (by field_simp [*] at *))
              (add safe 100 (by ring))
              (add safe 100 (by field_simp))
              (add safe 100 (by norm_num))
              (add safe 100 (by interval_cases))
              (add safe 0 (by split))
              (add safe 100 (by rfl))
              (add safe 100 (by decide))
              (add safe 0 (by push_cast))
              (add safe 100 (by assumption_mod_cast))
              (add norm 0 (by grind only [mul_div_cancel_left]))
              (add norm 0 (by grind only [mul_div_cancel_right]))
              (add norm 0 (by grind only [mul_div_cancel]))
              (add norm 0 (by grind only [div_mul_div_cancel']))
              (add norm 0 (by grind only [QuadraticForm.polar]))
              (add norm 0 (by grind only [mul_div_mul_comm]))
              (add norm 0 (by grind only [div_mul_cancel]))
              (add norm 0 (by grind only [div_div_div_cancel_right']))
              (add norm 0 (by grind only [WeakFEPair.Λ]))
              (add norm 0 (by grind only [ContinuousAlternatingMap.sub_apply]))
              (add norm 0 (by grind only [MultilinearMap.map_add_sub_map_add_sub_linearDeriv]))
              (add norm 0 (by grind only [CliffordAlgebra.contractLeft_ι_mul]))
              (add norm 0 (by grind only [sub_eq_add]))
              (add norm 0 (by grind only [AddConstMapClass.map_sub_nsmul]))
              (add norm 0 (by grind only [LinearMap.BilinForm.sub_right]))
              (add norm 0 (by grind only [QuadraticForm.map_sub]))
              (add norm 0 (by grind only [AddCommGroup.modEq_sub_iff_add_modEq]))
              (add norm 0 (by grind only [CliffordAlgebra.ι_mul_ι_add_swap]))
              (add norm 0 (by grind only [LinearPMap.map_sub]))
              (add norm 0 (by grind only [sub_smul]))
              (add norm 0 (by grind only [AddConstMapClass.map_sub_one]))
              (add norm 0 (by grind only [WeakFEPair.functional_equation]))
              (add norm 0 (by grind only [div_self']))
              (add norm 0 (by grind only [AddConstMapClass.map_sub_const]))
              (add norm 0 (by grind only [WeakFEPair.functional_equation₀]))
              (add norm 0 (by grind only [mul_div_right_comm]))
              (add safe 0 (by simp only [div_mul] at *))
              (add safe 0 (by simp only [div_div] at *))
              (add safe 0 (by simp only [mul_div] at *))
              (add safe 0 (by simp only [sub_div] at *))
              (add safe 0 (by simp only [mul_div_assoc] at *))
              (add unsafe 50% (by grind only [eq_div_iff_mul_eq']))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   simp_all only [mul_one, sub_add_cancel]
        -- [P25.18] = Δ_r (1 − p_k)
        _ = (rs - rf) * (1 - provingProb Astar (ascent Astar rs rf α l₀ k)) := by
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * -
          aesop (config := {
              maxRuleApplications := 100
              maxNormIterations := 320
              maxGoals := 512
              enableSimp := false
            })
              (add norm 100 (by norm_cast))
              (add norm 0 (by linarith))
              (add norm 0 (by nlinarith))
              (add norm 0 (by omega))
              (add norm 1 (by push_neg))
              (add norm 100 (by gcongr))
              (add norm 0 (by bound))
              (add norm 0 (by ring_nf))
              (add norm 100 (by exfalso))
              (add norm 1 (by field_simp [*] at *))
              (add safe 100 (by ring))
              (add safe 100 (by field_simp))
              (add safe 100 (by norm_num))
              (add safe 100 (by positivity))
              (add safe 100 (by interval_cases))
              (add safe 0 (by ext))
              (add safe 0 (by split))
              (add safe 0 (by norm_num [*] at *))
              (add safe 100 (by rfl))
              (add safe 100 (by decide))
              (add safe 0 (by push_cast))
              (add safe 100 (by assumption_mod_cast))
              (add norm 0 (by grind only [mul_div_cancel_right]))
              (add norm 0 (by grind only [mul_div_cancel_left]))
              (add norm 0 (by grind only [mul_div_cancel]))
              (add norm 0 (by grind only [sub_eq_add]))
              (add norm 0 (by grind only [div_mul_div_cancel']))
              (add norm 0 (by grind only [div_mul_cancel]))
              (add norm 0 (by grind only [div_self']))
              (add norm 0 (by grind only [SubgroupClass.coe_div]))
              (add norm 0 (by grind only [div_div_div_cancel_right']))
              (add norm 0 (by grind only [QuadraticForm.polar]))
              (add norm 0 (by grind only [mul_div_mul_comm]))
              (add norm 0 (by grind only [AddCommGroup.modEq_sub_iff_add_modEq]))
              (add norm 0 (by grind only [div_one]))
              (add norm 0 (by grind only [AddConstMapClass.map_sub_nsmul]))
              (add norm 0 (by grind only [WeakFEPair.Λ]))
              (add norm 0 (by grind only [div_le_iff_le_mul]))
              (add norm 0 (by grind only [half_add_self]))
              (add norm 0 (by grind only [div_eq_mul_inv]))
              (add norm 0 (by grind only [ContinuousAlternatingMap.sub_apply]))
              (add norm 0 (by grind only [tsub_div]))
              (add norm 0 (by grind only [le_div_iff_mul_le]))
              (add norm 0 (by grind only [WeakFEPair.functional_equation]))
              (add norm 0 (by grind only [AddConstMapClass.map_sub_const]))
              (add norm 0 (by grind only [div_le_iff_le_mul']))
              (add norm 0 (by grind only [MultilinearMap.map_add_sub_map_add_sub_linearDeriv]))
              (add norm 0 (by grind only [AddConstMapClass.map_sub_zsmul]))
              (add safe 0 (by simp only [div_mul] at *))
              (add safe 0 (by simp only [div_div] at *))
              (add safe 0 (by simp only [mul_div] at *))
              (add safe 0 (by simp only [sub_div] at *))
              (add safe 0 (by simp only [mul_div_assoc] at *))
              (add safe 0 (by simp only [add_div] at *))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   (linarith)
    -- [P25.19] Δ_r (1 − p_k) ≥ Δ_r (1 − 2p_0), ∀ k ≤ k̄   (P25.9)
    have h19 : (rs - rf) * (1 - 2 * p₀) ≤ (rs - rf) * (1 - provingProb Astar (ascent Astar rs rf α l₀ k)) := by
      -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
      -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
      clear * - h9 hk hr
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
          (add norm 100 (by simp_all))
          (add norm 1 (by field_simp [*] at *))
          (add safe 100 (by field_simp))
          (add safe 100 (by norm_num))
          (add safe 100 (by positivity))
          (add safe 100 (by omega))
          (add safe 100 (by interval_cases))
          (add safe 0 (by ext))
          (add safe 0 (by split))
          (add safe 100 (by rfl))
          (add safe 100 (by decide))
          (add safe 0 (by push_cast))
          (add safe 100 (by assumption_mod_cast))
          (add norm 0 (by grind only [le_div_iff_mul_le]))
          (add norm 0 (by grind only [mul_le_mul_left]))
          (add norm 0 (by grind only [le_div_iff]))
          (add norm 0 (by grind only [div_le_iff_le_mul]))
          (add norm 0 (by grind only [le_div_iff_mul_le']))
          (add norm 0 (by rw [mul_le_mul_iff_left]))
          (add norm 0 (by grind only [div_le_iff]))
          (add norm 0 (by grind only [div_le_iff_le_mul']))
          (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
          (add norm 0 (by grind only [mul_le_mul_iff_right]))
          (add norm 0 (by grind only [mul_le_mul]))
          (add norm 0 (by grind only [div_le_iff']))
          (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
          (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
          (add norm 0 (by grind only [div_le_div_iff_left]))
          (add norm 0 (by grind only [mul_le_mul_left']))
          (add norm 0 (by grind only [mul_le_mul_right']))
          (add norm 0 (by grind only [mul_le_of_le_one_left]))
          (add norm 0 (by grind only [one_add_mul_le_pow]))
          (add norm 0 (by grind only [CircleDeg1Lift.translationNumber_le_of_le_add_int]))
          (add norm 0 (by grind only [SzemerediRegularity.hundred_le_m]))
          (add unsafe 50% (by nlinarith [mul_le_mul_right]))
          (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
          (add unsafe 50% (by nlinarith [Real.pi_le_four]))
          (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
          (add unsafe 50% (by nlinarith [le_div_iff']))
          (add unsafe 50% (by nlinarith [div_le_one]))
          (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
          (add unsafe 50% (by nlinarith [div_le_div_iff]))
          (add unsafe 50% (by nlinarith [le_of_mul_le_mul_left]))
          (add unsafe 50% (by nlinarith [div_le_div_right]))
          (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
      --   simp_all only [one_div, mul_inv_rev, sub_pos, mul_le_mul_iff_right₀, tsub_le_iff_right, c, p₀]
      --   (ring_nf)
      --   (grind only [le_div_iff_mul_le])
    exact ⟨heq, h19⟩
  -- [P25.20] Hence reaching any suboptimality ε < Δ_r(1 − 2p_0) requires more than k̄ steps
  have h20 : ∀ ε : ℝ, ε < (rs - rf) * (1 - 2 * p₀) → ∀ k : ℕ, optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k) ≤ ε → 1 / (2 * c * p₀) < k := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - hfirst
    intro δ hδ k h
    contrapose! h
    specialize hfirst k h
    rw [hfirst.1]
    exact lt_of_lt_of_le hδ hfirst.2
  -- [P25.21] With Θ(1) verifications per step, N(ε) ∈ Ω(k̄) = Ω(1/p_0)
  have h21 : ∀ V : ℕ → ℕ, (∀ k, k ≤ V k) → ∀ ε : ℝ, ε < (rs - rf) * (1 - 2 * p₀) → ∀ k : ℕ, optReward Astar rs rf - expectedReward Astar rs rf (ascent Astar rs rf α l₀ k) ≤ ε → 1 / (2 * c * p₀) < V k := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - h20
    intro V hV
    intro ε hε k hk
    specialize h20 ε hε k hk
    apply lt_of_lt_of_le h20
    exact_mod_cast hV k
  exact ⟨hfirst, h20, h21⟩

/-- Remark 2.6: at a uniform initialization (`π^{(h)}(m ∣ C) = 1/M` for every `h` and `m`), every arm
has probability `M^{−H}`, i.e., `π(·∣C)` is uniform over `𝒜`. -/
theorem policy_of_uniform (l : Logits H M) (hl : ∀ h m, softmax l h m = 1 / (M : ℝ))
    (A : Arm H M) : policy l A = 1 / (M : ℝ) ^ H := by
  -- [R26.5] At a uniform initialization, π(·|C) is itself uniform over 𝒜: π(A|C) = M^{−H}
  have h5 : policy l A = 1 / (M : ℝ) ^ H := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - hl
    simp [policy, hl]
  exact h5

/-- Remark 2.6: at a uniform initialization, `p_0 = |𝒜*| M^{−H}`. -/
theorem provingProb_of_uniform (Astar : Finset (Arm H M)) (l : Logits H M)
    (hl : ∀ h m, softmax l h m = 1 / (M : ℝ)) :
    provingProb Astar l = Astar.card / (M : ℝ) ^ H := by
  -- [cite: policy_of_uniform] π(A|C) = M^{−H} for every arm
  have h5 : ∀ A : Arm H M, policy l A = 1 / (M : ℝ) ^ H := fun A => policy_of_uniform l hl A
  -- [R26.2] so p_0 = |𝒜*| M^{−H}
  have h2 : provingProb Astar l = Astar.card / (M : ℝ) ^ H := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - h5
    simp [provingProb, h5]
    rfl
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
  have h3 : 1 / (2 * (2 * α * ((H : ℝ) * M) * (rs - rf)) * provingProb Astar l₀) = (M : ℝ) ^ H / (4 * α * ((H : ℝ) * M) * (rs - rf) * Astar.card) := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - hp0
    field_simp [hp0]
    rw [hp0]
    field_simp <;> norm_cast <;> ring
  -- [conclusion]
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
  clear * - h20 hp0 h3 hε hk
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
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
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by nlinarith [mul_lt_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right']))
      (add unsafe 50% (by nlinarith [mul_lt_mul']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
      (add unsafe 50% (by nlinarith [mul_lt_mul₀]))
      (add unsafe 50% (by nlinarith [mul_lt_mul'']))
      (add unsafe 50% (by nlinarith [div_lt_div_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt']))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_le_of_lt]))
      (add unsafe 50% (by nlinarith [mul_add_mul_lt_mul_add_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_lt_of_le]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [lt_of_mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [lt_div_iff']))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_right']))
      (add unsafe 50% (by nlinarith [lt_of_mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [Real.lt_log_iff_exp_lt]))
      (add unsafe 50% (by nlinarith [StrictConvexOn.slope_strict_mono_adjacent]))
      (add unsafe 50% (by nlinarith [lt_of_le_of_lt]))
      (add unsafe 50% (by nlinarith [Real.pi_lower_bound_start]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [pow_lt_pow_right₀]))
      (add unsafe 50% (by nlinarith [div_lt_iff']))
      (add unsafe 50% (by nlinarith [mul_self_lt_mul_self]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [tsub_le_iff_right, one_div, mul_inv_rev, inv_div, gt_iff_lt]
  --   (bound)

/-- Remark 2.6, "for H = 1, `p₀ = 1/M`", with its assumption `|𝒜*| = 1` made explicit; in general,
for `H = 1`, `p₀ = |𝒜*|/M ≥ 1/M`. -/
theorem provingProb_zero_single (hM : 0 < M) (Astar : Finset (Arm 1 M)) (h1 : Astar.card = 1) :
    provingProb Astar (0 : Logits 1 M) = 1 / (M : ℝ) := by
  -- [cite: provingProb_of_uniform] at l = 0 (uniform by softmax_zero), H = 1: p_0 = |𝒜*| M^{−1}
  have hp := provingProb_of_uniform Astar (0 : Logits 1 M) (softmax_zero hM)
  -- [R26.4] A single component (H=1) with a single optimal arm (|𝒜*|=1) has p_0 = 1/M
  have h4 : provingProb Astar (0 : Logits 1 M) = 1 / (M : ℝ) := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 3 round(s) and 24 candidate t_C; none proves it.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - hp h1
    rw [hp, h1]
    simp
  exact h4

end Sec2.DSP
