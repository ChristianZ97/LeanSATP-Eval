import Mathlib

/-! The five modules of the Chapter 2 formalization (`project/Sec2/*.lean`) and the five modules of its DSP version
(`project/Sec2/DSP/*.lean`) in one file, so that it can be checked with `lake env lean` like the other proofs in this
repository. The private lemma `sum_exp_pos`, defined in three modules, is renamed `sum_exp_pos_SelfBound` and
`sum_exp_pos_Plateau` in this file. Each DSP module is a `section` of its own, so its `set_option maxHeartbeats 0`
applies to that module only. -/

-- ===== project/Sec2/Basic.lean =====
section

/-!
# Setup of Chapter 2 (Remark "Setup" in §2.2 of the thesis, and Eq. (2.1))

Fix a context `C`. An arm has `H` components, and each component has `M` levels; for simplicity,
the Setup in the thesis sets every `M_h = M`, and so do we here. The network's output for `C` is
the logits `l ∈ ℝ^{HM}`, with one real number `l_h^m` per component `h` and level `m`.
Gradients and 2-norms are taken in `EuclideanSpace ℝ (Fin H × Fin M)`, i.e., the thesis's `‖·‖₂`.
-/

open Finset

namespace Sec2

/-- Logits `l ∈ ℝ^{HM}`: one real number `l_h^m` per component `h` and level `m`. -/
abbrev Logits (H M : ℕ) := EuclideanSpace ℝ (Fin H × Fin M)

/-- An arm (one complete configuration) assigns each component `h` a level `v_h`. -/
abbrev Arm (H M : ℕ) := Fin H → Fin M

variable {H M : ℕ}

/-- The softmax of component `h`: `π^{(h)}(m ∣ C) = e^{l_h^m} / Σ_{m'} e^{l_h^{m'}}`. -/
noncomputable def softmax (l : Logits H M) (h : Fin H) (m : Fin M) : ℝ :=
  Real.exp (l (h, m)) / ∑ m' : Fin M, Real.exp (l (h, m'))

/-- Eq. (2.1): with each component sampled independently, `π(A ∣ C) = ∏_h π^{(h)}(v_h ∣ C)`.
In the thesis, (2.1) splits the product into three groups: `K` retrieved lemmas, `|𝕋|` candidate
tactics, and `B` budget options; here the three groups share one index `h : Fin H`
(`H = K + |𝕋| + B`), as written in the Setup and in the proof of Lemma 2.3. -/
noncomputable def policy (l : Logits H M) (A : Arm H M) : ℝ :=
  ∏ h : Fin H, softmax l h (A h)

/-- The proving probability `p_s = Σ_{A ∈ 𝒜*} π(A ∣ C)`, where `𝒜*` is the set of arms that
prove the subgoal. -/
noncomputable def provingProb (Astar : Finset (Arm H M)) (l : Logits H M) : ℝ :=
  ∑ A ∈ Astar, policy l A

/-- The reward `R(C, A)`: `r_success` if `A ∈ 𝒜*`, and `r_failure` otherwise.
The thesis defines `𝒜* = {A : R(C, A) = r_success}` in terms of `R`; the two formulations are
equivalent when `r_success ≠ r_failure`. -/
def reward (Astar : Finset (Arm H M)) (rs rf : ℝ) (A : Arm H M) : ℝ :=
  if A ∈ Astar then rs else rf

/-- The objective for a fixed context: `J_sparse(l) = E_{A ∼ π(·∣C)}[R(C, A)]`. -/
noncomputable def expectedReward (Astar : Finset (Arm H M)) (rs rf : ℝ) (l : Logits H M) : ℝ :=
  ∑ A : Arm H M, policy l A * reward Astar rs rf A

/-! ## Basic properties -/

/-- Over a nonempty finite set, `Σ_j e^{x_j}` is positive. -/
private lemma sum_exp_pos {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    0 < ∑ j, Real.exp (x j) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  positivity

/-- The softmax denominator `Σ_{m'} e^{l_h^{m'}}` is positive when there is a level `m`. -/
private lemma softmax_denom_pos (l : Logits H M) (h : Fin H) (m : Fin M) :
    0 < ∑ m' : Fin M, Real.exp (l (h, m')) := by
  have : Nonempty (Fin M) := ⟨m⟩
  exact sum_exp_pos fun m' => l (h, m')

/-- `e^a / S` is positive when the denominator `S` is positive. -/
private lemma exp_div_pos (a S : ℝ) (hS : 0 < S) :
    0 < Real.exp a / S := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
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
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.exp_log]))
      (add norm 0 (by grind only [Real.exp_add]))
      (add norm 0 (by grind only [Real.exp_sub]))
      (add norm 0 (by grind only [Real.exp]))
      (add norm 0 (by grind only [Real.exp_mul]))
      (add norm 0 (by grind only [Real.exp_eq_exp_ℝ]))
      (add norm 0 (by grind only [Real.exp_neg]))
      (add norm 0 (by grind only [Real.exp_ne_zero]))
      (add norm 0 (by grind only [Real.log_exp]))
      (add norm 0 (by grind only [rexp_neg_deriv_aux]))
      (add norm 0 (by grind only [rexp_neg_injOn_aux]))
      (add norm 0 (by grind only [integral_exp]))
      (add norm 0 (by grind only [Real.exp_nat_mul]))
      (add norm 0 (by grind only [Real.exp_one_rpow]))
      (add safe 0 (by nlinarith [Real.pi_pos]))
      (add unsafe 50% (by nlinarith [Behrend.exp_neg_two_mul_le]))
      (add unsafe 50% (by nlinarith [Real.exp_pos]))
      (add unsafe 50% (by nlinarith [Real.rpow_def_of_pos]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_exp]))
      (add unsafe 50% (by nlinarith [HurwitzKernelBounds.exp_lt_aux]))
      (add unsafe 50% (by nlinarith [Real.add_one_lt_exp]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_one_iff]))
      (add unsafe 50% (by nlinarith [Real.exp_bound_div_one_sub_of_interval']))
      (add unsafe 50% (by nlinarith [Behrend.div_lt_floor]))
      (add unsafe 50% (by nlinarith [MeasureTheory.integral_exp_pos]))
      (add unsafe 50% (by nlinarith [Real.log_rpow]))
      (add unsafe 50% (by nlinarith [Real.rpow_pos_of_pos]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [Real.add_one_lt_exp_of_pos]))
      (add unsafe 50% (by nlinarith [Behrend.bound]))
      (add unsafe 50% (by nlinarith [Real.mul_pos]))
      (add unsafe 50% (by nlinarith [div_lt_one]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [div_pos_iff_of_pos_right]
  --   (bound)

theorem softmax_pos (l : Logits H M) (h : Fin H) (m : Fin M) : 0 < softmax l h m := by
  unfold softmax
  exact exp_div_pos _ _ (softmax_denom_pos l h m)

/-- `Σ_i x_i / Σ_j x_j = 1` when the sum is nonzero (normalized weights sum to 1). -/
private lemma sum_div_sum_eq_one {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∑ j, x j ≠ 0) :
    ∑ i, x i / ∑ j, x j = 1 := by
  -- [satp + generative rule] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- The generator g (an Opus 5.5 subagent) supplies t_C = `Finset.univ x (Inv.inv (∑ ι, x ι))` as the arguments of lemma ℓ = `Finset.mul_sum` in rule 24 of A.
  -- Rule type, priority, position, wrapper and ℓ are unchanged, so A′ differs from A only by t_C; arguments drawn only
  -- from names in the context do not prove the subgoal (thesis Section 5.5):
  --   A : (add norm 0 (by grind only [Finset.mul_sum]))
  --   A′: (add norm 0 (by grind only [Finset.mul_sum Finset.univ x (Inv.inv (∑ ι, x ι))]))
  -- Proof body: the full A′ (A is the `satp?` output, port 5170; only the rule above and indentation changed).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 16
    })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 100 (by exfalso))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_const_one]))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add norm 0 (by grind only [Finset.mul_sum Finset.univ x (Inv.inv (∑ ι, x ι))]))
      (add norm 0 (by grind only [inner_sum_smul_sum_smul_of_sum_eq_zero]))
      (add norm 0 (by grind only [Finset.prod_eq_one]))
      (add norm 0 (by grind only [Finset.sum_div]))
      (add norm 0 (by grind only [Finset.sum_mul]))
      (add norm 0 (by grind only [Finset.prod_le_prod']))
      (add norm 0 (by grind only [Finset.sum_smul]))
      (add norm 0 (by grind only [FiniteField.sum_pow_lt_card_sub_one]))
      (add norm 0 (by grind only [Finset.prod_singleton]))
      (add norm 0 (by grind only [Lagrange.eval_interpolate_not_at_node']))
      (add norm 0 (by grind only [Finset.prod_pow]))
      (add safe 0 (by simp only [div_self] at *))
      (add unsafe 90% (by rw [Finset.prod_div_distrib]))
      (add unsafe 90% (by rw [Finset.univ]))
      (add unsafe 90% (by rw [Finset.prod]))
      (add unsafe 90% (by rw [Finset.prod_const]))
      (add unsafe 90% (by rw [Finset.prod_eq_zero]))
      (add unsafe 90% (by rw [Fintype.prod_eq_one]))
      (add unsafe 90% (by rw [Finset.prod_apply]))
      (add unsafe 90% (by rw [Finset.prod_erase_mul]))
      (add unsafe 90% (by rw [EuclideanGeometry.inner_weightedVSub]))
      (add unsafe 90% (by rw [Fintype.prod_congr]))
      (add unsafe 90% (by rw [Affine.Simplex.sum_pointsWithCircumcenter]))
      (add unsafe 90% (by rw [Finset.prod_eq_single_of_mem]))
      (add unsafe 90% (by rw [Finset.single_le_prod']))
      (add unsafe 90% (by rw [Finset.prod_attach]))
      (add unsafe 90% (by rw [Finset.sum_smul_vsub_eq_weightedVSub_sub]))
      (add unsafe 90% (by rw [Finset.mem_univ]))
      (add unsafe 90% (by rw [Finset.prod_comm]))
      (add unsafe 90% (by rw [div_self']))
  -- The `aesop?` "Try this" output with A′, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [ne_eq]
  --   (ring)
  --   (ring)
  --   (grind only [Finset.mul_sum Finset.univ x (Inv.inv (∑ ι, x ι))])

theorem sum_softmax (hM : 0 < M) (l : Logits H M) (h : Fin H) :
    ∑ m : Fin M, softmax l h m = 1 := by
  unfold softmax
  exact sum_div_sum_eq_one (fun m => Real.exp (l (h, m))) (softmax_denom_pos l h ⟨0, hM⟩).ne'

theorem policy_pos (l : Logits H M) (A : Arm H M) : 0 < policy l A :=
  Finset.prod_pos fun h _ => softmax_pos l h (A h)

/-- Interchanging sum and product: `Σ_{A : ι → κ} ∏_i σ_i(A_i) = ∏_i Σ_k σ_i(k)`. -/
private lemma sum_pi_prod_eq_prod_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (σ : ι → κ → ℝ) :
    ∑ A : ι → κ, ∏ i, σ i (A i) = ∏ i, ∑ k, σ i k := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 4 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  revert σ
  intros σ
  rw [← Fintype.prod_sum]

/-- `π(·∣C)` is a probability distribution over `𝒜`. -/
theorem sum_policy (hM : 0 < M) (l : Logits H M) : ∑ A : Arm H M, policy l A = 1 := by
  -- `Σ_A ∏_h π^{(h)}(v_h) = ∏_h Σ_m π^{(h)}(m)` (components are independent); each factor is 1.
  unfold policy
  exact (sum_pi_prod_eq_prod_sum fun h m => softmax l h m).trans
    (Finset.prod_eq_one fun h _ => sum_softmax hM l h)

theorem provingProb_nonneg (Astar : Finset (Arm H M)) (l : Logits H M) :
    0 ≤ provingProb Astar l :=
  Finset.sum_nonneg fun A _ => (policy_pos l A).le

theorem provingProb_pos (Astar : Finset (Arm H M)) (hA : Astar.Nonempty) (l : Logits H M) :
    0 < provingProb Astar l :=
  Finset.sum_pos (fun A _ => policy_pos l A) hA

/-- The sum over a subset `s` of nonnegative weights that sum to 1 is at most 1. -/
private lemma sum_le_one_of_sum_eq_one {ι : Type*} [Fintype ι] (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    ∑ i ∈ s, p i ≤ 1 := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [← h1]
  exact Finset.sum_le_univ_sum_of_nonneg hp

theorem provingProb_le_one (hM : 0 < M) (Astar : Finset (Arm H M)) (l : Logits H M) :
    provingProb Astar l ≤ 1 := by
  unfold provingProb
  exact sum_le_one_of_sum_eq_one Astar (fun A => policy l A) (fun A => (policy_pos l A).le)
    (sum_policy hM l)

/-- The expected-reward term of a single arm:
`π · R = Δ_r · (π if A ∈ 𝒜*, else 0) + r_failure · π`. -/
private lemma mul_ite_split (p rs rf : ℝ) (b : Prop) [Decidable b] :
    p * (if b then rs else rf) = (rs - rf) * (if b then p else 0) + rf * p := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      useDefaultSimpSet := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 0 (by gcongr))
      (add safe 100 (by interval_cases))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_ite]))
      (add norm 0 (by grind only [ite_mul]))
      (add norm 0 (by grind only [Complex.cpow_def]))
      (add norm 0 (by grind only [ite_self]))
      (add norm 0 (by grind only [ite_apply]))
      (add norm 0 (by grind only [mul_boole]))
      (add norm 0 (by grind only [ite_and]))
      (add norm 0 (by grind only [ite_pow]))
      (add norm 0 (by grind only [tprod_ite_eq]))
      (add norm 0 (by grind only [if_true]))
      (add norm 0 (by grind only [ite_ite_comm]))
      (add norm 0 (by grind only [ite_true]))
      (add norm 0 (by grind only [if_pos]))
      (add norm 0 (by grind only [ite_not]))
      (add norm 0 (by grind only [ite_false]))
      (add norm 0 (by grind only [ite]))
      (add norm 0 (by grind only [if_neg]))
      (add norm 0 (by grind only [Finset.prod_ite_eq]))
      (add norm 0 (by grind only [Finset.prod_ite_eq']))
      (add norm 0 (by grind only [pow_ite]))
      (add norm 0 (by grind only [boole_mul]))
      (add norm 0 (by grind only [Quaternion.star_mul_eq_coe]))
      (add norm 0 (by grind only [apply_ite]))
      (add norm 0 (by grind only [Finset.filter_eq]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [if_congr]))
      (add norm 0 (by grind only [Quaternion.star_mul_self]))
      (add norm 0 (by grind only [if_false]))
      (add norm 0 (by grind only [EReal.coe_mul]))
      (add norm 0 (by grind only [Quaternion.mul_star_eq_coe]))
      (add norm 0 (by grind only [Finsupp.single_apply]))
      (add norm 0 (by grind only [IsAdjoinRootMonic.coeff_apply]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (bound)

/-- Linearity of finite sums: if `Σ_i g_i = 1`, then `Σ_i (a f_i + b g_i) = a Σ_i f_i + b`. -/
private lemma sum_mul_add_mul_of_sum_eq_one {ι : Type*} [Fintype ι] (f g : ι → ℝ) (a b : ℝ)
    (hg : ∑ i, g i = 1) :
    ∑ i, (a * f i + b * g i) = a * ∑ i, f i + b := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hg, mul_one]

/-- Setup: with the context fixed, `J_sparse = Δ_r · p_s + r_failure`, where
`Δ_r = r_success − r_failure`. -/
theorem expectedReward_eq (hM : 0 < M) (Astar : Finset (Arm H M)) (rs rf : ℝ) (l : Logits H M) :
    expectedReward Astar rs rf l = (rs - rf) * provingProb Astar l + rf := by
  unfold expectedReward provingProb reward
  calc ∑ A : Arm H M, policy l A * (if A ∈ Astar then rs else rf)
      = ∑ A : Arm H M, ((rs - rf) * (if A ∈ Astar then policy l A else 0) + rf * policy l A) :=
        Finset.sum_congr rfl fun A _ => mul_ite_split (policy l A) rs rf (A ∈ Astar)
    _ = (rs - rf) * ∑ A : Arm H M, (if A ∈ Astar then policy l A else 0) + rf :=
        sum_mul_add_mul_of_sum_eq_one _ _ _ _ (sum_policy hM l)
    -- `Σ_A 𝟙(A ∈ 𝒜*) π(A) = Σ_{A ∈ 𝒜*} π(A)` (Mathlib's `Fintype.sum_ite_mem`).
    _ = (rs - rf) * ∑ A ∈ Astar, policy l A + rf :=
        congrArg (fun t => (rs - rf) * t + rf) (Fintype.sum_ite_mem Astar fun A => policy l A)

/-! ## Differentiability
The softmax denominator is always positive, so `p_s` and `J_sparse` are smooth in the logits. -/

/-- A coordinate `l ↦ l_i` on Euclidean space is a continuous linear map, hence differentiable. -/
private lemma differentiable_coord {ι : Type*} [Fintype ι] (i : ι) :
    Differentiable ℝ (fun l : EuclideanSpace ℝ ι => l i) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (`satp?` did not finish within 900 s and was terminated).
  -- Generative rule: the search of A reaches no lemma rule into which t_C could be inserted, so thesis Section 5.5 does not apply.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  fun_prop

/-- The quotient of two differentiable real functions is differentiable when the denominator
is nowhere zero. -/
private lemma differentiable_div_of_ne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c d : E → ℝ) (hc : Differentiable ℝ c) (hd : Differentiable ℝ d) (hne : ∀ x, d x ≠ 0) :
    Differentiable ℝ (fun x => c x / d x) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (`satp?` did not finish within 900 s and was terminated).
  -- Generative rule: the search of A reaches no lemma rule into which t_C could be inserted, so thesis Section 5.5 does not apply.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  intro x
  simp only [div_eq_inv_mul]
  exact DifferentiableAt.mul (DifferentiableAt.inv (hd x) (hne x)) (hc x)

/-- Each `π^{(h)}(m ∣ C)` is differentiable in the logits: the numerator and the denominator are
differentiable, and the denominator is always positive. -/
private lemma differentiable_softmax (h : Fin H) (m : Fin M) :
    Differentiable ℝ (fun l : Logits H M => softmax l h m) := by
  have hnum : Differentiable ℝ (fun l : Logits H M => Real.exp (l (h, m))) :=
    (differentiable_coord (h, m)).exp
  have hden : Differentiable ℝ (fun l : Logits H M => ∑ m' : Fin M, Real.exp (l (h, m'))) :=
    Differentiable.fun_sum fun m' _ => (differentiable_coord (h, m')).exp
  have hne : ∀ l : Logits H M, ∑ m' : Fin M, Real.exp (l (h, m')) ≠ 0 := fun l =>
    (softmax_denom_pos l h m).ne'
  unfold softmax
  exact differentiable_div_of_ne _ _ hnum hden hne

/-- A product of finitely many differentiable real functions is differentiable. -/
private lemma differentiable_finsetProd {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Finset ι) (f : ι → E → ℝ) (hf : ∀ i, Differentiable ℝ (f i)) :
    Differentiable ℝ (fun x => ∏ i ∈ s, f i x) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (`satp?` did not finish within 900 s and was terminated).
  -- Generative rule: the search of A reaches no lemma rule into which t_C could be inserted, so thesis Section 5.5 does not apply.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  induction s using Finset.induction_on
  · simp [differentiable_const]
  · simp [Finset.prod_insert, *]
  · exact Classical.typeDecidableEq ι

/-- The `π(A ∣ C)` of Eq. (2.1) is a product of `H` softmaxes, so it is differentiable. -/
private lemma differentiable_policy (A : Arm H M) :
    Differentiable ℝ (fun l : Logits H M => policy l A) :=
  differentiable_finsetProd Finset.univ (fun h l => softmax l h (A h))
    (fun h => differentiable_softmax h (A h))

/-- `p_s` is differentiable everywhere in the logits (no assumptions needed). -/
theorem differentiable_provingProb (Astar : Finset (Arm H M)) :
    Differentiable ℝ (provingProb Astar) :=
  Differentiable.fun_sum (u := Astar) (A := fun A l => policy l A)
    fun A _ => differentiable_policy A

/-- `J_sparse` is differentiable everywhere in the logits (no assumptions needed). Mathlib's
`gradient` is defined as 0 at points where the function is not differentiable; this lemma
guarantees that the `gradient (expectedReward Astar rs rf) l` in Lemma 2.3 and `ascentStep`
is the thesis's `∇_l J_sparse`. -/
theorem differentiable_expectedReward (Astar : Finset (Arm H M)) (rs rf : ℝ) :
    Differentiable ℝ (expectedReward Astar rs rf) :=
  Differentiable.fun_sum (u := Finset.univ) (A := fun A l => policy l A * reward Astar rs rf A)
    fun A _ => (differentiable_policy A).mul_const _

/-- Adding a constant does not change the gradient: `∇(f + d) = ∇f`. -/
private lemma gradient_add_const_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (d : ℝ) (x : E) :
    gradient (fun y => f y + d) x = gradient f x := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [gradient, gradient, fderiv_add_const]

/-- For `f` differentiable at `x`, the gradient of a constant multiple is `∇(c f)(x) = c ∇f(x)`. -/
private lemma gradient_const_mul_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (c : ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
    gradient (fun y => c * f y) x = c • gradient f x := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  dsimp [gradient]
  rw [fderiv_const_mul hf]
  rw [map_smul]

/-- Setup: `∇_l J_sparse = Δ_r ∇_l p_s` (by `expectedReward_eq`). -/
theorem gradient_expectedReward (hM : 0 < M) (Astar : Finset (Arm H M)) (rs rf : ℝ)
    (l : Logits H M) :
    gradient (expectedReward Astar rs rf) l = (rs - rf) • gradient (provingProb Astar) l := by
  have hJ : expectedReward Astar rs rf = fun l' => (rs - rf) * provingProb Astar l' + rf :=
    funext (expectedReward_eq hM Astar rs rf)
  rw [hJ, gradient_add_const_eq]
  exact gradient_const_mul_eq (provingProb Astar) (rs - rf) l (differentiable_provingProb Astar l)

/-- The Riesz isomorphism is an isometry, so the norm of the gradient equals the operator norm
of `fderiv` (a linear functional). -/
private lemma norm_gradient_eq_norm_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  dsimp [gradient, fderiv]
  exact LinearIsometryEquiv.norm_map _ _

/-- The operator norm of a composition of two continuous linear maps is at most the product of
the norms: `‖A ∘ B‖ ≤ ‖B‖ · ‖A‖`. -/
private lemma opNorm_comp_le_mul {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : F →L[ℝ] G) (B : E →L[ℝ] F) :
    ‖A.comp B‖ ≤ ‖B‖ * ‖A‖ := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [mul_comm]
  exact ContinuousLinearMap.opNorm_comp_le A B

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
  have hJ : DifferentiableAt ℝ (expectedReward Astar rs rf) (net θ) :=
    differentiable_expectedReward Astar rs rf (net θ)
  -- Rewrite the gradient norms on both sides as operator norms of `fderiv`, then use the
  -- chain rule `D(J ∘ net) = DJ ∘ D net`.
  rw [norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv, fderiv_comp' θ hJ hnet]
  exact opNorm_comp_le_mul _ _

end Sec2

end

-- ===== project/Sec2/SelfBound.lean =====
section

/-!
# Lemma 2.3 (Self-bounding gradient)

Thesis: `‖∇_l J_sparse‖₂ ≤ √(HM) · Δ_r · p_s`.
-/

open Finset

namespace Sec2

variable {H M : ℕ}

/-! ### Auxiliary lemmas for the proof (following the thesis's proof of Lemma 2.3) -/

/-! #### Derivative of the softmax along `l + t · e_{(h,m)}` -/

/-- Moving by `t` along `e_{(h,m)}`: the entry `(h, a)` becomes `l_h^a + t · 𝟙(a = m)`. -/
private lemma line_apply_same {H M : ℕ} (l : EuclideanSpace ℝ (Fin H × Fin M)) (h : Fin H)
    (m a : Fin M) (t : ℝ) :
    (l + t • EuclideanSpace.single (h, m) (1 : ℝ)) (h, a) =
      l (h, a) + t * (if a = m then 1 else 0) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
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
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
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
      (add norm 0 (by grind only [ContinuousLinearMap.add_apply]))
      (add norm 0 (by grind only [ContinuousLinearMap.map_add]))
      (add norm 0 (by grind only [ContinuousLinearMap.mul_apply]))
      (add norm 0 (by grind only [mul_one]))
      (add norm 0 (by grind only [ContinuousLinearMap.coe_add]))
      (add norm 0 (by grind only [MeasureTheory.L1.setToL1_add_left']))
      (add norm 0 (by grind only [ContinuousLinearMap.coe_mul]))
      (add norm 0 (by grind only [MeasureTheory.L1.setToL1_add_left]))
      (add norm 0 (by grind only [ContinuousMultilinearMap.add_apply]))
      (add norm 0 (by grind only [DMatrix.add_apply]))
      (add norm 0 (by grind only [ContinuousLinearMap.mul_def]))
      (add norm 0 (by grind only [Finsupp.add_apply]))
      (add norm 0 (by grind only [Pi.mul_apply]))
      (add norm 0 (by grind only [Finsupp.coe_add]))
      (add norm 0 (by grind only [LeftInvariantDerivation.coe_add]))
      (add norm 0 (by grind only [LieDerivation.add_apply]))
      (add norm 0 (by grind only [one_mul]))
      (add norm 0 (by grind only [ContinuousLinearMap.one_apply]))
      (add norm 0 (by grind only [DFinsupp.coe_add]))
      (add norm 0 (by grind only [DFinsupp.add_apply]))
      (add norm 0 (by grind only [ContinuousLinearMap.coe_smul]))
      (add norm 0 (by grind only [Submodule.coe_add]))
      (add norm 0 (by grind only [ContinuousLinearMap.coe_smul']))
      (add norm 0 (by grind only [MeasureTheory.setToFun_add_left']))
      (add norm 0 (by grind only [ContinuousLinearMap.add_compLpL]))
      (add norm 0 (by grind only [PiLp.add_apply]))
      (add norm 0 (by grind only [EuclideanSpace.single_apply]))
      (add norm 0 (by grind only [LinearIsometryEquiv.map_add]))
      (add norm 0 (by grind only [CategoryTheory.Mat.add_apply]))
      (add norm 0 (by grind only [lp.coeFn_add]))
      (add norm 0 (by grind only [ContinuousLinearMap.coe_add']))
      (add norm 0 (by grind only [ContinuousAlternatingMap.add_apply]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply, Prod.mk.injEq, true_and, smul_eq_mul,
  --   mul_ite, mul_one, mul_zero]

/-- One-dimensional exponential: the derivative of `t ↦ exp(x + t c)` at `0` is `exp(x) c`. -/
private lemma hasDerivAt_exp_line (x c : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (x + t * c)) (Real.exp x * c) 0 := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [mul_comm]
  convert (((hasDerivAt_id (0 : ℝ)).mul_const c).const_add x).exp using 1
  simp
  ring

/-- The softmax denominator is positive: if there is a level `a`, then `Σ_{m'} e^{x_{m'}} > 0`. -/
private lemma sum_exp_pos_SelfBound {M : ℕ} (x : Fin M → ℝ) (a : Fin M) :
    0 < ∑ m' : Fin M, Real.exp (x m') := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  apply Finset.sum_pos
  · exact fun a _ ↦ Real.exp_pos (x a)
  · exists a
    apply Finset.mem_univ

/-- The line `t ↦ x + t c` is at `x` when `t = 0`: `x + 0 · c = x`. -/
private lemma add_zero_mul_eq (x c : ℝ) : x + 0 * c = x := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [MulZeroClass]))
      (add norm 0 (by grind only [IsLprojection.mul_compl_self]))
      (add norm 0 (by grind only [gronwallBound_ε0]))
      (add norm 0 (by grind only [mul_self]))
      (add norm 0 (by grind only [LaurentPolynomial.T_zero]))
      (add norm 0 (by grind only [EReal.coe_zero]))
      (add norm 0 (by grind only [Quaternion.im_re]))
      (add norm 0 (by grind only [EReal.coe_mul]))
      (add norm 0 (by grind only [IsLprojection.coe_compl]))
      (add norm 0 (by grind only [DualNumber.snd_eps]))
      (add norm 0 (by grind only [WeierstrassCurve.ψ_zero]))
      (add norm 0 (by grind only [Real.exp_zero]))
      (add norm 0 (by grind only [zero_div]))
      (add norm 0 (by grind only [TrivSqZeroExt.inl_fst_add_inr_snd_eq]))
      (add norm 0 (by grind only [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [HurwitzZeta.oddKernel_def']))
      (add norm 0 (by grind only [add_self]))
      (add norm 0 (by grind only [gronwallBound_K0]))
      (add norm 0 (by grind only [IsLprojection.distrib_lattice_lemma]))
      (add norm 0 (by grind only [HurwitzZeta.evenKernel_def]))
      (add norm 0 (by grind only [Real.arccos_zero]))
      (add norm 0 (by grind only [Real.rpow_def]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [TrivSqZeroExt.inl_zero]))
      (add norm 0 (by grind only [EReal.coe_ennreal_ofReal]))
      (add norm 0 (by grind only [TrivSqZeroExt.exp_def_of_smul_comm]))
      (add norm 0 (by grind only [mul_ite]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_inl]))
      (add norm 0 (by grind only [Complex.exp_zero]))
      (add norm 0 (by grind only [EReal.coe_coe_sign]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (linarith)

/-- Multiplying by an indicator and summing leaves one term: `Σ_{m'} f(m') 𝟙(m' = m) = f(m)`. -/
private lemma sum_mul_ite_eq {M : ℕ} (f : Fin M → ℝ) (m : Fin M) :
    ∑ m' : Fin M, f m' * (if m' = m then 1 else 0) = f m := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 16
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 100 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [mul_ite]))
      (add norm 0 (by grind only [Finset.prod_ite_eq]))
      (add norm 0 (by grind only [Finset.prod_eq_single]))
      (add norm 0 (by grind only [Matrix.mul_apply]))
      (add norm 0 (by grind only [Finset.prod_const_one]))
      (add norm 0 (by grind only [Finset.prod_ite_eq']))
      (add norm 0 (by grind only [Fintype.prod_eq_single]))
      (add norm 0 (by grind only [mul_boole]))
      (add norm 0 (by grind only [FinVec.sum_eq]))
      (add norm 0 (by grind only [Finset.prod_eq_single_of_mem]))
      (add norm 0 (by grind only [SimpleGraph.degree_eq_sum_if_adj]))
      (add norm 0 (by grind only [Matrix.sum_apply]))
      (add norm 0 (by grind only [Matrix.dotProduct]))
      (add norm 0 (by grind only [AddChar.sum_mulShift]))
      (add norm 0 (by grind only [Finset.sum_boole]))
      (add norm 0 (by grind only [boole_mul]))
      (add norm 0 (by grind only [ite_mul]))
      (add norm 0 (by grind only [Finset.prod_singleton]))
      (add norm 0 (by grind only [Fintype.prod_eq_one]))
      (add norm 0 (by grind only [Finset.prod_eq_one]))
      (add norm 0 (by grind only [Finset.prod_apply]))
      (add norm 0 (by grind only [Matrix.mul_adjugate_apply]))
      (add norm 0 (by grind only [FiniteField.sum_pow_units]))
      (add norm 0 (by grind only [Matrix.mulVec]))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [Finset.prod_eq_zero]))
      (add norm 0 (by grind only [Matrix.transpose_apply]))
      (add norm 0 (by grind only [pow_ite]))
      (add norm 0 (by grind only [ite_true]))
      (add norm 0 (by grind only [SimpleGraph.dotProduct_mulVec_adjMatrix]))
      (add norm 0 (by grind only [Matrix.vecMul]))
      (add unsafe 90% (by rw [Finset.univ]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]

/-- The quotient rule gives the softmax derivative:
`(E_a / S)(c − E_m / S) = (E_a c S − E_a E_m) / S²`. -/
private lemma div_mul_sub_div_eq (Ea Em S c : ℝ) (hS : S ≠ 0) :
    Ea / S * (c - Em / S) = (Ea * c * S - Ea * Em) / S ^ 2 := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the search of A reaches no lemma rule into which t_C could be inserted, so thesis Section 5.5 does not apply.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  cases' eq_or_ne S 0 with h h <;> field_simp [hS] <;> ring

/-- The softmax derivative: `∂_{l_h^m} π^{(h)}(a) = π^{(h)}(a) (𝟙(a = m) − π^{(h)}(m))`. -/
private lemma hasDerivAt_softmax_line (l : Logits H M) (h : Fin H) (m a : Fin M) :
    HasDerivAt (fun t : ℝ => softmax (l + t • EuclideanSpace.single (h, m) (1 : ℝ)) h a)
      (softmax l h a * ((if a = m then 1 else 0) - softmax l h m)) 0 := by
  have hfun : (fun t : ℝ => softmax (l + t • EuclideanSpace.single (h, m) (1 : ℝ)) h a) =
      fun t => Real.exp (l (h, a) + t * (if a = m then 1 else 0)) /
        ∑ m' : Fin M, Real.exp (l (h, m') + t * (if m' = m then 1 else 0)) := by
    funext t
    simp only [softmax, line_apply_same l h m]
  have hnum := hasDerivAt_exp_line (l (h, a)) (if a = m then 1 else 0)
  have hden := HasDerivAt.fun_sum (u := univ)
    (fun m' _ => hasDerivAt_exp_line (l (h, m')) (if m' = m then 1 else 0))
  have hq := hnum.div hden
    (sum_exp_pos_SelfBound (fun m' => l (h, m') + 0 * (if m' = m then 1 else 0)) a).ne'
  simp only [add_zero_mul_eq] at hq
  rw [sum_mul_ite_eq (fun m' => Real.exp (l (h, m'))) m] at hq
  rw [hfun]
  unfold softmax
  rw [div_mul_sub_div_eq _ _ _ _ (sum_exp_pos_SelfBound (fun m' => l (h, m')) a).ne']
  exact hq

/-! #### Partial derivatives of `π(A ∣ C)` and `p_s` -/

/-- Moving by `t` along `e_{(h,m)}`: the entries of every other component `h' ≠ h` are unchanged. -/
private lemma line_apply_of_ne {H M : ℕ} (l : EuclideanSpace ℝ (Fin H × Fin M)) (h h' : Fin H)
    (hh : h' ≠ h) (m a : Fin M) (t : ℝ) :
    (l + t • EuclideanSpace.single (h, m) (1 : ℝ)) (h', a) = l (h', a) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_one]))
      (add norm 0 (by grind only [one_mul]))
      (add norm 0 (by grind only [ContinuousLinearMap.add_apply]))
      (add norm 0 (by grind only [ContinuousLinearMap.map_add]))
      (add norm 0 (by grind only [MeasureTheory.L1.setToL1_add_left']))
      (add norm 0 (by grind only [ContinuousLinearMap.mul_apply]))
      (add norm 0 (by grind only [MeasureTheory.L1.setToL1_add_left]))
      (add norm 0 (by grind only [ContinuousLinearMap.mul_def]))
      (add norm 0 (by grind only [CategoryTheory.Biprod.ofComponents_comp]))
      (add norm 0 (by grind only [ContinuousLinearMap.coe_mul]))
      (add norm 0 (by grind only [mul_self]))
      (add norm 0 (by grind only [ContinuousLinearMap.coe_add]))
      (add norm 0 (by grind only [ContinuousMultilinearMap.add_apply]))
      (add norm 0 (by grind only [LeftInvariantDerivation.coe_add]))
      (add norm 0 (by grind only [MeasureTheory.setToFun_add_left']))
      (add norm 0 (by grind only [DFinsupp.coe_add]))
      (add norm 0 (by grind only [DirectSum.gMulLHom]))
      (add norm 0 (by grind only [LieDerivation.add_apply]))
      (add norm 0 (by grind only [CategoryTheory.Mat.add_apply]))
      (add norm 0 (by grind only [ContinuousLinearMap.one_apply]))
      (add norm 0 (by grind only [MeasureTheory.Integrable.toL1_add]))
      (add norm 0 (by grind only [Finsupp.add_apply]))
      (add norm 0 (by grind only [Pi.mul_apply]))
      (add norm 0 (by grind only [DMatrix.add_apply]))
      (add norm 0 (by grind only [Submodule.coe_add]))
      (add norm 0 (by grind only [ContinuousLinearMap.add_compLpL]))
      (add norm 0 (by grind only [Finsupp.coe_add]))
      (add norm 0 (by grind only [IsLprojection.mul_compl_self]))
      (add norm 0 (by grind only [ContinuousAlternatingMap.add_apply]))
      (add norm 0 (by grind only [PiLp.add_apply]))
      (add norm 0 (by grind only [DFinsupp.add_apply]))
      (add norm 0 (by grind only [ContinuousLinearMap.coe_add']))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [ne_eq, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply, Prod.mk.injEq, false_and,
  --   ↓reduceIte, smul_eq_mul, mul_zero, add_zero]

/-- Changing only `l_h^m` leaves the softmax of every other component `h' ≠ h` unchanged. -/
private lemma softmax_line_of_ne (l : Logits H M) {h h' : Fin H} (hh : h' ≠ h) (m a : Fin M)
    (t : ℝ) : softmax (l + t • EuclideanSpace.single (h, m) (1 : ℝ)) h' a = softmax l h' a := by
  simp only [softmax, line_apply_of_ne l h h' hh m]

/-- If every factor except the `h`-th equals `g h'`, the product is `(∏_{h' ≠ h} g h') · f h`. -/
private lemma prod_eq_prod_erase_mul {H : ℕ} (f g : Fin H → ℝ) (h : Fin H)
    (hf : ∀ h' ≠ h, f h' = g h') : ∏ h', f h' = (∏ h' ∈ univ.erase h, g h') * f h := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [← Finset.prod_erase_mul univ f (mem_univ h)]
  congr 1
  exact Finset.prod_congr rfl fun h' hh' => hf h' (ne_of_mem_erase hh')

/-- Merging the split-off factor back into the product:
`(∏_{h' ≠ h} f h') · (f h · (c − q)) = (∏_{h'} f h') · (c − q)`. -/
private lemma prod_erase_mul_mul_eq {H : ℕ} (f : Fin H → ℝ) (h : Fin H) (c q : ℝ) :
    (∏ h' ∈ univ.erase h, f h') * (f h * (c - q)) = (∏ h', f h') * (c - q) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [← mul_assoc]
  simp
  left
  apply Finset.prod_erase_mul
  simp

/-- `∂_{l_h^m} π(A ∣ C) = π(A ∣ C) (𝟙(v_h = m) − π^{(h)}(m ∣ C))`: `l_h^m` enters only
`π^{(h)}`. -/
private lemma hasDerivAt_policy_line (l : Logits H M) (A : Arm H M) (h : Fin H) (m : Fin M) :
    HasDerivAt (fun t : ℝ => policy (l + t • EuclideanSpace.single (h, m) (1 : ℝ)) A)
      (policy l A * ((if A h = m then 1 else 0) - softmax l h m)) 0 := by
  have hfun : (fun t : ℝ => policy (l + t • EuclideanSpace.single (h, m) (1 : ℝ)) A) =
      fun t => (∏ h' ∈ univ.erase h, softmax l h' (A h')) *
        softmax (l + t • EuclideanSpace.single (h, m) (1 : ℝ)) h (A h) := by
    funext t
    unfold policy
    exact prod_eq_prod_erase_mul
      (fun h' => softmax (l + t • EuclideanSpace.single (h, m) (1 : ℝ)) h' (A h'))
      (fun h' => softmax l h' (A h')) h fun h' hh' => softmax_line_of_ne l hh' m (A h') t
  have hd := (hasDerivAt_softmax_line l h m (A h)).const_mul
    (∏ h' ∈ univ.erase h, softmax l h' (A h'))
  rw [prod_erase_mul_mul_eq (fun h' => softmax l h' (A h')) h] at hd
  rw [hfun, policy]
  exact hd

/-- `∂_{l_h^m} p_s = Σ_{A ∈ 𝒜*} π(A ∣ C) (𝟙(v_h = m) − π^{(h)}(m ∣ C))` (along the line). -/
private lemma hasDerivAt_provingProb_line (Astar : Finset (Arm H M)) (l : Logits H M) (h : Fin H)
    (m : Fin M) :
    HasDerivAt (fun t : ℝ => provingProb Astar (l + t • EuclideanSpace.single (h, m) (1 : ℝ)))
      (∑ A ∈ Astar, policy l A * ((if A h = m then 1 else 0) - softmax l h m)) 0 := by
  unfold provingProb
  exact HasDerivAt.fun_sum fun A _ => hasDerivAt_policy_line l A h m

/-- If `f` is differentiable at `x`, the derivative `fderiv f x v` along direction `v` is the
derivative of `t ↦ f(x + t v)` at `0`. -/
private lemma fderiv_apply_eq_of_hasDerivAt_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (x v : E) (d : ℝ) (hf : DifferentiableAt ℝ f x)
    (hd : HasDerivAt (fun t : ℝ => f (x + t • v)) d 0) :
    fderiv ℝ f x v = d := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [← hf.lineDeriv_eq_fderiv]
  exact hd.deriv

/-- The partial derivative `∂_{l_h^m} p_s` (`p_s` is differentiable everywhere). -/
private lemma fderiv_provingProb_single (Astar : Finset (Arm H M)) (l : Logits H M) (h : Fin H)
    (m : Fin M) :
    fderiv ℝ (provingProb Astar) l (EuclideanSpace.single (h, m) 1) =
      ∑ A ∈ Astar, policy l A * ((if A h = m then 1 else 0) - softmax l h m) :=
  fderiv_apply_eq_of_hasDerivAt_line _ _ _ _ (differentiable_provingProb Astar l)
    (hasDerivAt_provingProb_line Astar l h m)

/-! #### `|∂_{l_h^m} p_s| ≤ p_s` -/

/-- The softmax value is at most 1: `e^{x_m} / Σ_{m'} e^{x_{m'}} ≤ 1`. -/
private lemma exp_div_sum_exp_le_one {M : ℕ} (x : Fin M → ℝ) (m : Fin M) :
    Real.exp (x m) / ∑ m' : Fin M, Real.exp (x m') ≤ 1 := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [div_le_one (Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨m, mem_univ m⟩)]
  exact Finset.single_le_sum (f := fun m' => Real.exp (x m'))
    (fun _ _ => (Real.exp_pos _).le) (mem_univ m)

/-- `π^{(h)}(m ∣ C) ≤ 1`. -/
private lemma softmax_le_one (l : Logits H M) (h : Fin H) (m : Fin M) : softmax l h m ≤ 1 := by
  unfold softmax
  exact exp_div_sum_exp_le_one (fun m' => l (h, m')) m

/-- If `s ∈ (0, 1]`, then `|1 − s| ≤ 1`. -/
private lemma abs_one_sub_le_one (s : ℝ) (h0 : 0 < s) (h1 : s ≤ 1) : |1 - s| ≤ 1 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 600
      maxNormIterations := 520
    })
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mabs_div_comm]))
      (add norm 0 (by grind only [mabs_of_one_lt]))
      (add norm 0 (by grind only [abs_div]))
      (add norm 0 (by grind only [mabs_of_one_le]))
      (add norm 0 (by grind only [abs_eq_self]))
      (add norm 0 (by grind only [Real.dist_eq]))
      (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq]))
      (add norm 0 (by grind only [abs_mul]))
      (add norm 0 (by grind only [mabs_lt]))
      (add norm 0 (by grind only [Real.abs_log_sub_add_sum_range_le]))
      (add norm 0 (by grind only [Int.abs_sub_lt_one_of_floor_eq_floor]))
      (add norm 0 (by grind only [Real.sin_bound]))
      (add norm 0 (by grind only [abs_one]))
      (add norm 0 (by grind only [Rat.dist_eq]))
      (add norm 0 (by grind only [ENNReal.abs_toReal]))
      (add norm 0 (by grind only [one_le_mabs]))
      (add norm 0 (by grind only [abs_lt_norm_sub_of_not_sameRay]))
      (add norm 0 (by grind only [abs_inv]))
      (add norm 0 (by grind only [mabs_of_lt_one]))
      (add norm 0 (by grind only [Nat.abs_cast]))
      (add norm 0 (by grind only [abs_le]))
      (add norm 0 (by grind only [Real.norm_eq_abs]))
      (add norm 0 (by grind only [Int.one_le_abs]))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [mabs_of_le_one]))
      (add norm 0 (by grind only [one_lt_mabs]))
      (add norm 0 (by grind only [Int.dist_eq]))
      (add norm 0 (by grind only [Complex.abs_abs]))
      (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul]))
      (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_one_sub_mul]))
      (add norm 0 (by grind only [Real.dist_le_of_mem_Icc]))
      (add norm 0 (by grind only [ArithmeticFunction.abs_moebius_le_one]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (grind only [abs_eq_self])

/-- If `s ∈ (0, 1]`, then `|0 − s| ≤ 1`. -/
private lemma abs_zero_sub_le_one (s : ℝ) (h0 : 0 < s) (h1 : s ≤ 1) : |0 - s| ≤ 1 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [abs_one]))
      (add norm 0 (by grind only [abs_eq_self]))
      (add norm 0 (by grind only [mabs_of_one_le]))
      (add norm 0 (by grind only [mabs_of_one_lt]))
      (add norm 0 (by grind only [mabs_one]))
      (add norm 0 (by grind only [mabs_inv]))
      (add norm 0 (by grind only [mabs_of_le_one]))
      (add norm 0 (by grind only [mabs_div_comm]))
      (add norm 0 (by grind only [ENNReal.abs_toReal]))
      (add norm 0 (by grind only [Nat.abs_cast]))
      (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq]))
      (add norm 0 (by grind only [one_le_mabs]))
      (add norm 0 (by grind only [mabs]))
      (add norm 0 (by grind only [mabs_of_lt_one]))
      (add norm 0 (by grind only [Int.one_le_abs]))
      (add norm 0 (by grind only [Real.abs_log_sub_add_sum_range_le]))
      (add norm 0 (by grind only [abs_inv]))
      (add norm 0 (by grind only [Real.sin_bound]))
      (add norm 0 (by grind only [ArithmeticFunction.abs_moebius_le_one]))
      (add norm 0 (by grind only [one_lt_mabs]))
      (add norm 0 (by grind only [NNReal.abs_eq]))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [abs_div]))
      (add norm 0 (by grind only [abs_mul]))
      (add norm 0 (by grind only [div_le_one']))
      (add norm 0 (by grind only [Int.abs_sub_lt_one_of_floor_eq_floor]))
      (add norm 0 (by grind only [Real.dist_eq]))
      (add norm 0 (by grind only [abs_pow]))
      (add norm 0 (by grind only [isLittleO_pow_pow_of_abs_lt_left]))
      (add norm 0 (by grind only [mabs_lt]))
      (add norm 0 (by grind only [ArithmeticFunction.abs_moebius_eq_one_of_squarefree]))
      (add norm 0 (by grind only [Hyperreal.coe_abs]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [zero_sub, abs_neg]
  --   (ring_nf)
  --   (grind only [abs_eq_self])

/-- `|𝟙(b = m) − π^{(h)}(m ∣ C)| ≤ 1`. -/
private lemma abs_indicator_sub_softmax_le (l : Logits H M) (h : Fin H) (m b : Fin M) :
    |(if b = m then (1 : ℝ) else 0) - softmax l h m| ≤ 1 := by
  split_ifs
  · exact abs_one_sub_le_one _ (softmax_pos l h m) (softmax_le_one l h m)
  · exact abs_zero_sub_le_one _ (softmax_pos l h m) (softmax_le_one l h m)

/-- The term of a single arm: if `P > 0` and `|c − s| ≤ 1`, then `|P (c − s)| ≤ P`. -/
private lemma abs_mul_sub_le (P c s : ℝ) (hP : 0 < P) (hc : |c - s| ≤ 1) :
    |P * (c - s)| ≤ P := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  have hP' : 0 < P := hP
  rewrite [abs_mul, mul_comm]
  simp_all [abs_eq_self.mpr hP.le]

/-- Triangle inequality: if `|f i| ≤ g i` for every term, then `|Σ_i f i| ≤ Σ_i g i`. -/
private lemma abs_sum_le_sum_of_abs_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (h : ∀ i ∈ s, |f i| ≤ g i) : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, g i := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  exact (Finset.abs_sum_le_sum_abs f s).trans (Finset.sum_le_sum h)

/-- `|∂_{l_h^m} p_s| ≤ p_s`, using the triangle inequality and `|𝟙(·) − π^{(h)}(m ∣ C)| ≤ 1`. -/
private lemma abs_sum_policy_mul_le (Astar : Finset (Arm H M)) (l : Logits H M) (h : Fin H)
    (m : Fin M) :
    |∑ A ∈ Astar, policy l A * ((if A h = m then 1 else 0) - softmax l h m)| ≤
      provingProb Astar l := by
  unfold provingProb
  exact abs_sum_le_sum_of_abs_le Astar _ _ fun A _ =>
    abs_mul_sub_le _ _ _ (policy_pos l A) (abs_indicator_sub_softmax_le l h m (A h))

/-! #### Summing the `HM` squared partial derivatives -/

/-- The `i`-th entry of the gradient is the partial derivative along `e_i`. -/
private lemma gradient_apply_eq_fderiv_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    gradient f x i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ ι)
    (x := EuclideanSpace.single i 1) (y := fderiv ℝ f x)
  rw [← h, real_inner_comm, EuclideanSpace.inner_single_left]
  simp [gradient]

/-- Squaring the bound on an entry: if `|g| ≤ p`, then `‖g‖² ≤ p²`. -/
private lemma norm_sq_le_sq_of_abs_le (g p : ℝ) (h : |g| ≤ p) : ‖g‖ ^ 2 ≤ p ^ 2 := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  norm_num
  cases abs_cases g <;> nlinarith

/-- Summing a constant over the `HM` entries: `Σ_{(h,m)} p² = HM · p²`. -/
private lemma sum_const_sq_eq (H M : ℕ) (p : ℝ) :
    ∑ _i : Fin H × Fin M, p ^ 2 = (H : ℝ) * M * p ^ 2 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Nat.cast_sum]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [Finset.prod_const]))
      (add norm 0 (by rw [Nat.cast_pow]))
      (add norm 0 (by grind only [Nat.cast_prod]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by rw [Nat.cast_npow]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Finset.card_fin]))
      (add norm 0 (by grind only [sq_sum_le_card_mul_sum_sq]))
      (add norm 0 (by grind only [nsmul_eq_mul]))
      (add norm 0 (by rw [Nat.cast_ofNat]))
      (add norm 0 (by grind only [Finset.sum_mul]))
      (add norm 0 (by grind only [pow_two_pow_sub_pow_two_pow]))
      (add norm 0 (by grind only [Finset.prod]))
      (add norm 0 (by grind only [Finset.prod_pow]))
      (add norm 0 (by grind only [Finset.prod_natCast]))
      (add norm 0 (by grind only [Nat.matrixOf_eval_descPochhammer_eq_mul_matrixOf_choose]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [CharTwo.sum_sq]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by rw [Quaternion.coe_natCast]))
      (add norm 0 (by grind only [Finset.card_univ]))
      (add norm 0 (by grind only [MvPolynomial.NewtonIdentities.esymm_to_weight]))
      (add norm 0 (by grind only [geom_sum₂_mul]))
      (add norm 0 (by grind only [gaussSum]))
      (add norm 0 (by grind only [Int.cast_ofNat]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]

/-- If `p ≥ 0`, then `√(HM · p²) = √(HM) · p`. -/
private lemma sqrt_mul_sq_eq (H M : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    Real.sqrt ((H : ℝ) * M * p ^ 2) = Real.sqrt ((H : ℝ) * M) * p := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
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
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [Real.rpow_two]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [norm_add_sq]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [norm_add_sq_real]))
      (add norm 0 (by grind only [PiLp.norm_eq_of_L2]))
      (add norm 0 (by grind only [EuclideanSpace.dist_eq]))
      (add norm 0 (by grind only [mul_self_nonneg]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_coe_center_sq]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [abs_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [pow_succ_nonneg, Real.sqrt_mul', Nat.cast_nonneg, Real.sqrt_mul, Real.sqrt_sq]

/-- `‖∇_l p_s‖₂ ≤ √(HM) · p_s`, by summing the `HM` squared partial derivatives. -/
private lemma norm_gradient_provingProb_le (Astar : Finset (Arm H M)) (l : Logits H M) :
    ‖gradient (provingProb Astar) l‖ ≤ Real.sqrt ((H : ℝ) * M) * provingProb Astar l := by
  have hcoord : ∀ i : Fin H × Fin M,
      |gradient (provingProb Astar) l i| ≤ provingProb Astar l := by
    rintro ⟨h, m⟩
    rw [gradient_apply_eq_fderiv_single, fderiv_provingProb_single Astar l h m]
    exact abs_sum_policy_mul_le Astar l h m
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i, ‖gradient (provingProb Astar) l i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin H × Fin M, provingProb Astar l ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => norm_sq_le_sq_of_abs_le _ _ (hcoord i))
    _ = Real.sqrt ((H : ℝ) * M * provingProb Astar l ^ 2) :=
        congrArg Real.sqrt (sum_const_sq_eq H M _)
    _ = Real.sqrt ((H : ℝ) * M) * provingProb Astar l :=
        sqrt_mul_sq_eq H M _ (provingProb_nonneg Astar l)

/-! #### Multiplying by `Δ_r` -/

/-- If `M = 0`, the right-hand side is 0: `0 ≤ √(H · 0) · (r_s − r_f) · p`. -/
private lemma zero_le_sqrt_mul_zero (H : ℕ) (rs rf p : ℝ) :
    (0 : ℝ) ≤ Real.sqrt ((H : ℝ) * ((0 : ℕ) : ℝ)) * (rs - rf) * p := by
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
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [div_zero]))
      (add norm 0 (by grind only [MulZeroClass]))
      (add norm 0 (by grind only [zero_div]))
      (add norm 0 (by grind only [Nat.cast_zero]))
      (add norm 0 (by grind only [Real.sqrt_zero]))
      (add norm 0 (by grind only [TrivSqZeroExt.inl_zero]))
      (add norm 0 (by grind only [EReal.coe_zero]))
      (add norm 0 (by grind only [Hyperreal.coe_zero]))
      (add norm 0 (by grind only [quadraticChar_zero]))
      (add norm 0 (by grind only [Zsqrtd.zero_re]))
      (add norm 0 (by grind only [Real.sqrt_eq_zero_of_nonpos]))
      (add norm 0 (by grind only [Quaternion.coe_zero]))
      (add norm 0 (by grind only [ZNum.cast_zero]))
      (add norm 0 (by grind only [FractionalIdeal.div_zero]))
      (add norm 0 (by grind only [Nat.floor_zero]))
      (add norm 0 (by grind only [Real.sin_zero]))
      (add norm 0 (by grind only [FiniteField.cast_card_eq_zero]))
      (add norm 0 (by grind only [zero_floorDiv]))
      (add norm 0 (by grind only [HasDerivWithinAt.deriv_eq_zero]))
      (add norm 0 (by grind only [MulChar.map_zero]))
      (add norm 0 (by grind only [quadraticCharFun_zero]))
      (add norm 0 (by grind only [torusIntegral_radius_zero]))
      (add norm 0 (by grind only [fourier_eval_zero]))
      (add norm 0 (by grind only [Rat.cast_zero]))
      (add norm 0 (by grind only [jacobiTheta₂'_undef]))
      (add norm 0 (by grind only [Int.cast_zero]))
      (add norm 0 (by grind only [zero_pow]))
      (add norm 0 (by grind only [Real.arccos_zero]))
      (add norm 0 (by grind only [harmonic_zero]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [Real.Angle.coe_zero]))
      (add unsafe 10% (by field_simp [Set.Icc.coe_zero] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [CharP.cast_eq_zero, mul_zero, Real.sqrt_zero, zero_mul, le_refl]

/-- Multiplying `g ≤ q p` by `Δ_r = r_s − r_f > 0`: `|Δ_r| · g ≤ q · Δ_r · p`. -/
private lemma abs_sub_mul_le (rs rf g q p : ℝ) (hr : rf < rs) (hg : g ≤ q * p) :
    |rs - rf| * g ≤ q * (rs - rf) * p := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [abs_of_pos (sub_pos.mpr hr)]
  nlinarith

/-- Lemma 2.3: for any logits `l`, `‖∇_l J_sparse(l)‖₂ ≤ √(HM) · Δ_r · p_s(l)`. -/
theorem norm_gradient_expectedReward_le (Astar : Finset (Arm H M)) (rs rf : ℝ) (hr : rf < rs)
    (l : Logits H M) :
    ‖gradient (expectedReward Astar rs rf) l‖ ≤
      Real.sqrt ((H : ℝ) * M) * (rs - rf) * provingProb Astar l := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have h0 : gradient (expectedReward Astar rs rf) l = 0 := Subsingleton.elim _ _
    rw [h0, norm_zero]
    exact zero_le_sqrt_mul_zero H rs rf (provingProb Astar l)
  · rw [gradient_expectedReward hM, norm_smul, Real.norm_eq_abs]
    exact abs_sub_mul_le rs rf _ _ _ hr (norm_gradient_provingProb_le Astar l)

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
  exact (norm_gradient_comp_le Astar rs rf net θ hnet).trans
    (mul_le_mul_of_nonneg_left (norm_gradient_expectedReward_le Astar rs rf hr (net θ))
      (norm_nonneg _))

end Sec2

end

-- ===== project/Sec2/Growth.lean =====
section

/-!
# Lemma 2.4 (Quadratic per-step growth)

Thesis: under gradient ascent on `l`, `l_{k+1} = l_k + α ∇_l J_sparse(l_k)`,
with a sufficiently small step size `α`,
`0 ≤ p_{k+1} − p_k ≤ c · p_k²`, where `c ∈ O(α · HM · Δ_r)`.

The formalization makes "sufficiently small" and `c` explicit: for the step-size bound
`α₀ = 1 / ((4H + 1) Δ_r)`, which depends only on `H` and `Δ_r`
(`4H + 1` is the constant of `provingProb_deriv2_bound`; with `1/` rather than `2/`, the proof
needs only the second-order remainder estimate without the `1/2`),
the inequality holds for all `0 < α ≤ α₀` and all `l`,
and `c = 2 α H M Δ_r`. The thesis states the lemma for the sequence `l_k`; here it is stated
for one step from an arbitrary `l`, and taking `l = l_k` gives every `k`.

The thesis proof uses "the bounded Hessian of the softmax" without proving it; here it is
stated as `provingProb_deriv2_bound`, which must be proved as well.
-/

open Finset

namespace Sec2

variable {H M : ℕ}

/-- One step of gradient ascent: `l ↦ l + α ∇_l J_sparse(l)`. -/
noncomputable def ascentStep (Astar : Finset (Arm H M)) (rs rf α : ℝ) (l : Logits H M) :
    Logits H M :=
  l + α • gradient (expectedReward Astar rs rf) l

/-! ### Auxiliary definitions and lemmas for `provingProb_deriv2_bound`

Along the line `s ↦ l + s δ`, with `a h m = l_h^m` and `d h m = δ_h^m`, write
`E = e^{a + s d}`, `Z_h = Σ_m E`, `σ_h(m) = E / Z_h` (the softmax), `μ_h = Σ_m σ_h(m) d_{h,m}`,
`Var_h = Σ_m σ_h(m) d_{h,m}² − μ_h²`, `π_A = ∏_h σ_h(A h)`, and `S_A = Σ_h (d_{h,A h} − μ_h)`.
Then `σ' = σ (d − μ)`, `μ' = Var`, `π_A' = π_A S_A`, and `S_A' = −Σ_h Var_h`,
so `p_s(l + s δ)'' = Σ_{A∈𝒜*} π_A (S_A² − Σ_h Var_h)`. -/

/-- `e^{l_h^m + s δ_h^m}`. -/
private noncomputable def d2E (a d : Fin H → Fin M → ℝ) (h : Fin H) (m : Fin M) (s : ℝ) : ℝ :=
  Real.exp (a h m + s * d h m)

/-- The softmax denominator `Z_h(s)`. -/
private noncomputable def d2Z (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) : ℝ :=
  ∑ m : Fin M, d2E a d h m s

/-- `σ_h(m)(s) = softmax (l + s δ) h m`. -/
private noncomputable def d2sig (a d : Fin H → Fin M → ℝ) (h : Fin H) (m : Fin M) (s : ℝ) : ℝ :=
  d2E a d h m s / d2Z a d h s

/-- `μ_h(s) = Σ_m σ_h(m)(s) d_{h,m}`. -/
private noncomputable def d2mu (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) : ℝ :=
  ∑ m : Fin M, d2sig a d h m s * d h m

/-- `Var_h(s) = Σ_m σ_h(m)(s) d_{h,m}² − μ_h(s)²`. -/
private noncomputable def d2var (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) : ℝ :=
  ∑ m : Fin M, d2sig a d h m s * d h m ^ 2 - d2mu a d h s ^ 2

/-- `π_A(s) = ∏_h σ_h(A h)(s)`. -/
private noncomputable def d2pi (a d : Fin H → Fin M → ℝ) (A : Arm H M) (s : ℝ) : ℝ :=
  ∏ h : Fin H, d2sig a d h (A h) s

/-- `S_A(s) = Σ_h (d_{h,A h} − μ_h(s))`. -/
private noncomputable def d2S (a d : Fin H → Fin M → ℝ) (A : Arm H M) (s : ℝ) : ℝ :=
  ∑ h : Fin H, (d h (A h) - d2mu a d h s)

/-! #### Numerical bounds -/

/-- The softmax denominator is positive: `Σ_m e^{x_m} > 0` when `M ≥ 1`. -/
private lemma sum_exp_pos_of_pos {M : ℕ} (hM : 0 < M) (x : Fin M → ℝ) :
    0 < ∑ m : Fin M, Real.exp (x m) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  try apply Finset.sum_pos
  · exact fun i _hi ↦ Real.exp_pos (x i)
  · existsi ⟨0, hM⟩
    simp

private lemma d2Z_pos (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) :
    0 < d2Z a d h s := by
  exact sum_exp_pos_of_pos hM (fun m => a h m + s * d h m)

/-- The softmax probabilities are positive: `e^x / Z > 0` when `Z > 0`. -/
private lemma exp_div_pos_of_pos (x Z : ℝ) (hZ : 0 < Z) :
    0 < Real.exp x / Z := by
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
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.exp_pos]))
      (add norm 0 (by grind only [Real.exp_log]))
      (add norm 0 (by grind only [Real.exp_mul]))
      (add norm 0 (by grind only [Real.exp_add]))
      (add norm 0 (by grind only [Real.exp_sub]))
      (add norm 0 (by grind only [Real.exp]))
      (add norm 0 (by grind only [Real.exp_eq_exp_ℝ]))
      (add norm 0 (by grind only [Real.exp_ne_zero]))
      (add norm 0 (by grind only [Real.exp_neg]))
      (add norm 0 (by grind only [Real.log_exp]))
      (add norm 0 (by grind only [rexp_neg_deriv_aux]))
      (add norm 0 (by grind only [rexp_neg_injOn_aux]))
      (add norm 0 (by grind only [Real.exp_nat_mul]))
      (add norm 0 (by grind only [integral_exp]))
      (add norm 0 (by grind only [Real.exp_half]))
      (add norm 0 (by grind only [Real.exp_arsinh]))
      (add norm 0 (by grind only [Real.exp_one_rpow]))
      (add norm 0 (by grind only [rexp_neg_image_aux]))
      (add safe 0 (by nlinarith [Real.pi_pos]))
      (add unsafe 50% (by nlinarith [Behrend.exp_neg_two_mul_le]))
      (add unsafe 50% (by nlinarith [Real.rpow_def_of_pos]))
      (add unsafe 50% (by nlinarith [HurwitzKernelBounds.exp_lt_aux]))
      (add unsafe 50% (by nlinarith [Real.exp_lt_exp]))
      (add unsafe 50% (by nlinarith [Real.add_one_lt_exp]))
      (add unsafe 50% (by nlinarith [Real.exp_bound_div_one_sub_of_interval']))
      (add unsafe 50% (by nlinarith [Real.exp_lt_one_iff]))
      (add unsafe 50% (by nlinarith [MeasureTheory.integral_exp_pos]))
      (add unsafe 50% (by nlinarith [Real.log_rpow]))
      (add unsafe 50% (by nlinarith [Behrend.div_lt_floor]))
      (add unsafe 50% (by nlinarith [Behrend.bound]))
      (add unsafe 50% (by nlinarith [Real.add_one_lt_exp_of_pos]))
      (add unsafe 50% (by nlinarith [Real.rpow_pos_of_pos]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [div_pos_iff_of_pos_right]
  --   (bound)

private lemma d2sig_pos (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (h : Fin H) (m : Fin M) (s : ℝ) :
    0 < d2sig a d h m s := by
  exact exp_div_pos_of_pos (a h m + s * d h m) (d2Z a d h s) (d2Z_pos hM a d h s)

/-- Normalized weights sum to 1: `Σ_m E_m / Σ_{m'} E_{m'} = 1` when the denominator is nonzero. -/
private lemma sum_div_sum_self_eq_one {M : ℕ} (E : Fin M → ℝ) (hZ : ∑ m : Fin M, E m ≠ 0) :
    ∑ m : Fin M, E m / ∑ m' : Fin M, E m' = 1 := by
  -- [satp + generative rule] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- The generator g (an Opus 5.5 subagent) supplies t_C = `Finset.univ E (Inv.inv (∑ m, E m))` as the arguments of lemma ℓ = `Finset.mul_sum` in rule 25 of A.
  -- Rule type, priority, position, wrapper and ℓ are unchanged, so A′ differs from A only by t_C; arguments drawn only
  -- from names in the context do not prove the subgoal (thesis Section 5.5):
  --   A : (add norm 0 (by grind only [Finset.mul_sum]))
  --   A′: (add norm 0 (by grind only [Finset.mul_sum Finset.univ E (Inv.inv (∑ m, E m))]))
  -- Proof body: the full A′ (A is the `satp?` output, port 5170; only the rule above and indentation changed).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 16
    })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 100 (by exfalso))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Finset.mul_sum Finset.univ E (Inv.inv (∑ m, E m))]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Finset.prod_div_distrib]))
      (add norm 0 (by grind only [Finset.sum_mul]))
      (add norm 0 (by grind only [Finset.sum_div]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [inner_sum_smul_sum_smul_of_sum_eq_zero]))
      (add norm 0 (by grind only [Finset.prod_const]))
      (add norm 0 (by grind only [Finpartition.coe_energy]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_eq_iff] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 0 (by simp only [mul_div_mul_left] at *))
      (add safe 0 (by simp only [mul_div_mul_right] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [two_ne_zero'] at *))
      (add safe 0 (by simp only [div_mul] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add unsafe 90% (by rw [Finset.prod]))
  -- The `aesop?` "Try this" output with A′, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [ne_eq]
  --   (ring)
  --   (ring)
  --   (grind only [Finset.mul_sum Finset.univ E (Inv.inv (∑ m, E m))])

private lemma d2sum_sig (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) :
    ∑ m : Fin M, d2sig a d h m s = 1 := by
  exact sum_div_sum_self_eq_one (fun m => d2E a d h m s) (d2Z_pos hM a d h s).ne'

/-- Each entry of a probability vector is at most 1: `σ_m ≤ 1` when `σ ≥ 0` and `Σ_m σ_m = 1`. -/
private lemma le_one_of_nonneg_of_sum_eq_one {M : ℕ} (σ : Fin M → ℝ) (h0 : ∀ m, 0 ≤ σ m)
    (h1 : ∑ m : Fin M, σ m = 1) (m : Fin M) :
    σ m ≤ 1 := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [← h1]
  exact Finset.single_le_sum (fun m _ ↦ h0 m) (Finset.mem_univ m)

private lemma d2sig_le_one (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (h : Fin H) (m : Fin M)
    (s : ℝ) : d2sig a d h m s ≤ 1 := by
  exact le_one_of_nonneg_of_sum_eq_one (fun m => d2sig a d h m s)
    (fun m => (d2sig_pos hM a d h m s).le) (d2sum_sig hM a d h s) m

/-- Expanding the square: `σ (x − μ)² = σ x² − 2μ (σ x) + μ² σ`. -/
private lemma mul_sub_sq_expand (σ x μ : ℝ) :
    σ * (x - μ) ^ 2 = σ * x ^ 2 - 2 * μ * (σ * x) + μ ^ 2 * σ := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by rw [Quaternion.coe_mul]))
      (add norm 0 (by rw [Quaternion.coe_commutes]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [sum_eight_sq_mul_sum_eight_sq]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Quaternion.star_mul_self]))
      (add norm 0 (by rw [Quaternion.coe_mul_eq_smul]))
      (add norm 0 (by grind only [Quaternion.star_mul_eq_coe]))
      (add norm 0 (by grind only [add_sq]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Quaternion.mul_star_eq_coe]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [gaussSum_sq]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [Pell.Solution₁.prop_x]))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))
      (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop_y]))
      (add unsafe 50% (by simp only [Pell.Solution₁.prop]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (linarith)

/-- Linearity of the sum: `Σ_m (f_m − c g_m + e k_m) = Σ_m f_m − c Σ_m g_m + e Σ_m k_m`. -/
private lemma sum_sub_mul_add_mul_eq {M : ℕ} (f g k : Fin M → ℝ) (c e : ℝ) :
    ∑ m : Fin M, (f m - c * g m + e * k m)
      = ∑ m : Fin M, f m - c * ∑ m : Fin M, g m + e * ∑ m : Fin M, k m := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_sub_distrib]

/-- Nonnegative weights give a nonnegative sum of squares: `Σ_m σ_m (d_m − μ)² ≥ 0` when `σ ≥ 0`. -/
private lemma sum_mul_sub_sq_nonneg {M : ℕ} (σ d : Fin M → ℝ) (μ : ℝ) (hσ : ∀ m, 0 ≤ σ m) :
    0 ≤ ∑ m : Fin M, σ m * (d m - μ) ^ 2 := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  exact Finset.sum_nonneg fun m _ => mul_nonneg (hσ m) (sq_nonneg _)

/-- `0 ≤ X = W − 2μ·μ + μ²·1` implies `μ² ≤ W`. -/
private lemma sq_le_of_nonneg_of_eq (X W μ : ℝ) (h1 : X = W - 2 * μ * μ + μ ^ 2 * 1)
    (h2 : 0 ≤ X) :
    μ ^ 2 ≤ W := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [pow_le_pow_left]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [two_ne_zero]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [sq_le_one_iff]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [one_le_div']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 90% (by simp only [pow_two] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   subst h1
  --   simp_all only [mul_one]
  --   (linarith)

/-- `μ_h² ≤ Σ_m σ_h(m) d_{h,m}²`, i.e., `Var_h ≥ 0`. -/
private lemma d2mu_sq_le (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) :
    d2mu a d h s ^ 2 ≤ ∑ m : Fin M, d2sig a d h m s * d h m ^ 2 := by
  have h1 : ∑ m : Fin M, d2sig a d h m s * (d h m - d2mu a d h s) ^ 2
      = ∑ m : Fin M, d2sig a d h m s * d h m ^ 2
        - 2 * d2mu a d h s * ∑ m : Fin M, d2sig a d h m s * d h m
        + d2mu a d h s ^ 2 * ∑ m : Fin M, d2sig a d h m s := by
    rw [Finset.sum_congr rfl fun m _ =>
      mul_sub_sq_expand (d2sig a d h m s) (d h m) (d2mu a d h s)]
    exact sum_sub_mul_add_mul_eq _ _ _ _ _
  have h2 : 0 ≤ ∑ m : Fin M, d2sig a d h m s * (d h m - d2mu a d h s) ^ 2 :=
    sum_mul_sub_sq_nonneg _ _ _ fun m => (d2sig_pos hM a d h m s).le
  have h3 : ∑ m : Fin M, d2sig a d h m s * d h m = d2mu a d h s := rfl
  rw [d2sum_sig hM, h3] at h1
  exact sq_le_of_nonneg_of_eq _ _ _ h1 h2

/-- `σ x² ≤ x²` when the weight is at most 1. -/
private lemma mul_sq_le_sq_of_le_one (σ x : ℝ) (hσ : σ ≤ 1) :
    σ * x ^ 2 ≤ x ^ 2 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
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
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [pow_le_pow_left]))
      (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add norm 0 (by grind only [one_le_pow_of_one_le]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_right]))
      (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add norm 0 (by grind only [sq_le_one_iff]))
      (add norm 0 (by grind only [le_mul_iff_one_le_right']))
      (add norm 0 (by grind only [sub_sq]))
      (add unsafe 90% (by simp only [one_le_sq_iff] at *))
      (add unsafe 90% (by simp only [one_le_two] at *))
      (add unsafe 90% (by simp only [zero_le_two] at *))
      (add unsafe 90% (by simp only [le_mul_of_one_le_right'] at *))
      (add unsafe 90% (by simp only [le_mul_of_one_le_left'] at *))
      (add unsafe 90% (by simp only [le_mul_of_one_le_left] at *))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 90% (by simp only [mul_le_mul_left] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (nlinarith)

private lemma d2wsum_le (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) :
    ∑ m : Fin M, d2sig a d h m s * d h m ^ 2 ≤ ∑ m : Fin M, d h m ^ 2 := by
  exact Finset.sum_le_sum fun m _ => mul_sq_le_sq_of_le_one _ _ (d2sig_le_one hM a d h m s)

private lemma d2var_nonneg (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) :
    0 ≤ d2var a d h s := by
  unfold d2var
  exact sub_nonneg.2 (d2mu_sq_le hM a d h s)

/-- Subtracting a square cannot increase the value: `W − μ² ≤ B` when `W ≤ B`. -/
private lemma sub_sq_le_of_le (W μ B : ℝ) (h : W ≤ B) :
    W - μ ^ 2 ≤ B := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [EisensteinSeries.auxbound2]))
      (add norm 0 (by grind only [EisensteinSeries.auxbound1]))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [sub_sq']))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add unsafe 90% (by simp only [pow_two] at *))
      (add unsafe 50% (by simp only [sq_sub_sq]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [tsub_le_iff_right]
  --   (nlinarith)

private lemma d2var_le (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) :
    d2var a d h s ≤ ∑ m : Fin M, d h m ^ 2 := by
  unfold d2var
  exact sub_sq_le_of_le _ _ _ (d2wsum_le hM a d h s)

/-- A single square is at most the sum of squares: `d_m² ≤ Σ_{m'} d_{m'}²`. -/
private lemma sq_le_sum_sq_self {M : ℕ} (d : Fin M → ℝ) (m : Fin M) :
    d m ^ 2 ≤ ∑ m' : Fin M, d m' ^ 2 := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  have : (0 : ℝ) ≤ ∑ m', d m' ^ 2
  · apply sum_nonneg
    intro i _
    apply sq_nonneg
  · exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (d i)) (Finset.mem_univ m)

/-- If both squares are at most `D`, the squared difference is at most `4D`: `(x − y)² ≤ 4D`. -/
private lemma sub_sq_le_four_mul_of_sq_le (x y D : ℝ) (h1 : x ^ 2 ≤ D) (h2 : y ^ 2 ≤ D) :
    (x - y) ^ 2 ≤ 4 * D := by
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
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [sub_sq]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [EisensteinSeries.auxbound2]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [EisensteinSeries.auxbound1]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [sq_pos_of_pos]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [norm_jacobiTheta₂_term_le]))
      (add norm 0 (by grind only [Real.sqrt_le_sqrt]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [EisensteinSeries.r1]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [abs_sq]))
      (add unsafe 50% (by simp only [sq_sub_sq]))
      (add unsafe 50% (by nlinarith [inv_div]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (nlinarith)

/-- Cauchy–Schwarz: `(Σ_{i<n} x_i)² ≤ n Σ_i x_i²`. -/
private lemma sq_sum_le_mul_sum_sq_fin {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, x i) ^ 2 ≤ n * ∑ i : Fin n, x i ^ 2 := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- Summing termwise bounds and multiplying by `n ≥ 0`: `n Σ_i y_i ≤ n Σ_i z_i` when every
`y_i ≤ z_i`. -/
private lemma mul_sum_le_mul_sum_of_le {n : ℕ} (y z : Fin n → ℝ) (h : ∀ i, y i ≤ z i) :
    (n : ℝ) * ∑ i : Fin n, y i ≤ n * ∑ i : Fin n, z i := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 16
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 100 (by exfalso))
      (add norm 100 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.prod_le_prod']))
      (add norm 0 (by grind only [Finset.prod_le_prod_of_subset_of_one_le']))
      (add norm 0 (by grind only [Finset.prod_le_prod]))
      (add norm 0 (by grind only [Finset.single_le_prod']))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [prod_le_tprod]))
      (add norm 0 (by grind only [Finset.prod_le_pow_card]))
      (add norm 0 (by grind only [fkg]))
      (add norm 0 (by grind only [Finset.sum_mul]))
      (add norm 0 (by grind only [norm_sum_le]))
      (add norm 0 (by grind only [MonovaryOn.sum_mul_sum_le_card_mul_sum]))
      (add norm 0 (by grind only [Nat.cast_sum]))
      (add norm 0 (by grind only [norm_prod_le]))
      (add norm 0 (by grind only [FormalMultilinearSeries.radius_right_inv_pos_of_radius_pos_aux1]))
      (add norm 0 (by grind only [Finset.prod_le_prod_of_subset']))
      (add norm 0 (by grind only [Finset.range]))
      (add norm 0 (by grind only [Finset.card_range]))
      (add norm 0 (by grind only [MeasureTheory.mul_upcrossingsBefore_le]))
      (add norm 0 (by grind only [sq_sum_le_card_mul_sum_sq]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Finset.sum_schlomilch_le']))
      (add norm 0 (by grind only [pow_le_pow_left]))
      (add norm 0 (by grind only [Finset.prod_range_mul_prod_Ico]))
      (add norm 0 (by grind only [pow_le_pow_left']))
      (add norm 0 (by grind only [VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le]))
      (add norm 0 (by grind only [Finset.norm_prod_le]))
      (add unsafe 90% (by rw [Finset.prod_le_univ_prod_of_one_le']))
      (add unsafe 90% (by rw [prod_le_hasProd]))
      (add unsafe 90% (by rw [Finset.prod_const]))
      (add unsafe 90% (by rw [Finset.prod]))
      (add unsafe 90% (by rw [Finset.univ]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (bound)

/-- Pulling the constant 4 out of the sum: `n Σ_i 4 D_i = 4 n Σ_i D_i`. -/
private lemma mul_sum_four_mul_eq {n : ℕ} (D : Fin n → ℝ) :
    (n : ℝ) * ∑ i : Fin n, 4 * D i = 4 * n * ∑ i : Fin n, D i := by
  -- [satp + generative rule] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- The generator g (an Opus 5.5 subagent) supplies t_C = `univ D 4` as the arguments of lemma ℓ = `Finset.sum_mul` in rule 23 of A.
  -- Rule type, priority, position, wrapper and ℓ are unchanged, so A′ differs from A only by t_C; arguments drawn only
  -- from names in the context do not prove the subgoal (thesis Section 5.5):
  --   A : (add norm 0 (by grind only [Finset.sum_mul]))
  --   A′: (add norm 0 (by grind only [Finset.sum_mul univ D 4]))
  -- Proof body: the full A′ (A is the `satp?` output, port 5171; only the rule above and indentation changed).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 16
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Finset.mul_sum]))
      (add norm 0 (by grind only [Finset.prod_mul_distrib]))
      (add norm 0 (by grind only [Finset.sum_mul univ D 4]))
      (add norm 0 (by grind only [Fin.prod_univ_succ]))
      (add norm 0 (by grind only [Finset.prod_comm]))
      (add norm 0 (by grind only [FinVec.sum_eq]))
      (add norm 0 (by grind only [Fin.prod_const]))
      (add norm 0 (by grind only [Finset.prod_sigma']))
      (add norm 0 (by grind only [bernstein.variance]))
      (add norm 0 (by grind only [Finset.prod_const]))
      (add norm 0 (by grind only [Nat.matrixOf_eval_descPochhammer_eq_mul_matrixOf_choose]))
      (add norm 0 (by grind only [Matrix.dotProduct]))
      (add norm 0 (by grind only [Finset.prod_range]))
      (add norm 0 (by grind only [Finset.card_fin]))
      (add norm 0 (by grind only [Matrix.mul_apply]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Finset.prod_le_prod']))
      (add norm 0 (by grind only [Behrend.sum_eq]))
      (add norm 0 (by grind only [ContinuousMultilinearMap.sum_apply]))
      (add norm 0 (by grind only [Finsupp.prod_pow]))
      (add norm 0 (by grind only [GaussianFourier.integral_cexp_neg_sum_mul_add]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [bernstein.probability]))
      (add norm 0 (by grind only [Fin.prod_univ_two]))
      (add norm 0 (by grind only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]))
      (add norm 0 (by grind only [Nat.cast_sum]))
      (add unsafe 90% (by rw [Finset.prod]))
      (add unsafe 90% (by rw [Fintype.prod_congr]))
      (add unsafe 90% (by rw [Finset.univ]))
      (add unsafe 90% (by rw [Finset.prod_apply]))
      (add unsafe 90% (by rw [Finset.prod_le_univ_prod_of_one_le']))
  -- The `aesop?` "Try this" output with A′, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (grind only [Finset.sum_mul univ D 4])

/-- `S_A² ≤ 4H ‖δ‖²` (Cauchy–Schwarz and `|d_{h,A h} − μ_h|² ≤ 4 Σ_m d_{h,m}²`). -/
private lemma d2S_sq_le (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (A : Arm H M) (s : ℝ) :
    d2S a d A s ^ 2 ≤ 4 * H * ∑ h : Fin H, ∑ m : Fin M, d h m ^ 2 := by
  have hterm : ∀ h : Fin H, (d h (A h) - d2mu a d h s) ^ 2 ≤ 4 * ∑ m : Fin M, d h m ^ 2 :=
    fun h => sub_sq_le_four_mul_of_sq_le _ _ _ (sq_le_sum_sq_self (d h) (A h))
      ((d2mu_sq_le hM a d h s).trans (d2wsum_le hM a d h s))
  unfold d2S
  exact (sq_sum_le_mul_sum_sq_fin _).trans
    ((mul_sum_le_mul_sum_of_le _ _ hterm).trans_eq (mul_sum_four_mul_eq _))

private lemma d2pi_nonneg (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (A : Arm H M) (s : ℝ) :
    0 ≤ d2pi a d A s := by
  unfold d2pi
  exact Finset.prod_nonneg fun h _ => (d2sig_pos hM a d h (A h) s).le

/-- The product of the distributions of the components is still a distribution:
`Σ_A ∏_h σ_h(A h) = 1` when every `Σ_m σ_h(m) = 1`. -/
private lemma sum_prod_eq_one_of_sum_eq_one {H M : ℕ} (σ : Fin H → Fin M → ℝ)
    (h1 : ∀ h, ∑ m : Fin M, σ h m = 1) :
    ∑ A : Fin H → Fin M, ∏ h : Fin H, σ h (A h) = 1 := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 4 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [← Fintype.prod_sum σ]
  simp [h1]

private lemma d2sum_pi_le_one (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (Astar : Finset (Arm H M))
    (s : ℝ) : ∑ A ∈ Astar, d2pi a d A s ≤ 1 := by
  calc ∑ A ∈ Astar, d2pi a d A s ≤ ∑ A : Arm H M, d2pi a d A s :=
        Finset.sum_le_univ_sum_of_nonneg fun A => d2pi_nonneg hM a d A s
    _ = 1 := sum_prod_eq_one_of_sum_eq_one (fun h m => d2sig a d h m s)
        fun h => d2sum_sig hM a d h s

/-! #### Derivatives -/

/-- Derivative of the exponential: `d/ds e^{a + s d} = e^{a + s d} · d`. -/
private lemma hasDerivAt_exp_affine (a d s : ℝ) :
    HasDerivAt (fun s => Real.exp (a + s * d)) (Real.exp (a + s * d) * d) s := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  exact ((hasDerivAt_mul_const d).const_add a).exp

private lemma hasDerivAt_d2E (a d : Fin H → Fin M → ℝ) (h : Fin H) (m : Fin M) (s : ℝ) :
    HasDerivAt (fun s => d2E a d h m s) (d2E a d h m s * d h m) s := by
  exact hasDerivAt_exp_affine (a h m) (d h m) s

private lemma hasDerivAt_d2Z (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) :
    HasDerivAt (fun s => d2Z a d h s) (∑ m : Fin M, d2E a d h m s * d h m) s := by
  unfold d2Z
  exact HasDerivAt.fun_sum fun m _ => hasDerivAt_d2E a d h m s

/-- Pulling the denominator out of the sum: `Σ_m (E_m / Z) d_m = (Σ_m E_m d_m) / Z`. -/
private lemma sum_div_mul_eq_sum_mul_div {M : ℕ} (E d : Fin M → ℝ) (Z : ℝ) :
    ∑ m : Fin M, E m / Z * d m = (∑ m : Fin M, E m * d m) / Z := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: genloop found an A′, but its t_C builds `fun i => E i * d i` from the combinators `Function.swap`, `Function.onFun` and `Function.eval`, which circumvents the ban on `fun`; by the author's ruling it is not counted.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  trans
  · apply Finset.sum_congr rfl
    · intro i _
      rfl
  · simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]

private lemma d2mu_eq (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) :
    d2mu a d h s = (∑ m : Fin M, d2E a d h m s * d h m) / d2Z a d h s := by
  exact sum_div_mul_eq_sum_mul_div (fun m => d2E a d h m s) (d h) (d2Z a d h s)

/-- Rearranging the quotient rule: `(E d Z − E T) / Z² = (E / Z)(d − T / Z)` when `Z ≠ 0`. -/
private lemma quotient_rule_eq_mul_sub (E dm Z T : ℝ) (hZ : Z ≠ 0) :
    (E * dm * Z - E * T) / Z ^ 2 = E / Z * (dm - T / Z) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the search of A reaches no lemma rule into which t_C could be inserted, so thesis Section 5.5 does not apply.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  field_simp <;> ring

/-- The softmax derivative: `σ' = σ (d − μ)`. -/
private lemma hasDerivAt_d2sig (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (h : Fin H) (m : Fin M)
    (s : ℝ) :
    HasDerivAt (fun s => d2sig a d h m s) (d2sig a d h m s * (d h m - d2mu a d h s)) s := by
  have hZ : d2Z a d h s ≠ 0 := (d2Z_pos hM a d h s).ne'
  refine ((hasDerivAt_d2E a d h m s).fun_div (hasDerivAt_d2Z a d h s) hZ).congr_deriv ?_
  rw [d2mu_eq]
  exact quotient_rule_eq_mul_sub _ _ _ _ hZ

/-- Expansion: `σ (x − μ) x = σ x² − μ (σ x)`. -/
private lemma mul_sub_mul_self_expand (σ x μ : ℝ) :
    σ * (x - μ) * x = σ * x ^ 2 - μ * (σ * x) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 512
      useDefaultSimpSet := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [div_inv_eq_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
      (add norm 0 (by grind only [Quaternion.mul_imJ]))
      (add norm 0 (by grind only [mul_neg]))
      (add norm 0 (by grind only [Quaternion.mul_re]))
      (add norm 0 (by grind only [Quaternion.mul_imI]))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [neg_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by grind only [CauSeq.const_neg]))
      (add norm 0 (by grind only [inv_mul']))
      (add norm 0 (by grind only [Quaternion.mul_imK]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_iff]))
      (add norm 0 (by grind only [Real.arccos_neg]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Quaternion.star_imI]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imK]))
      (add norm 0 (by rw [Quaternion.star_mul_eq_coe]))
      (add norm 0 (by grind only [Quaternion.star_imJ]))
      (add norm 0 (by grind only [Function.Antiperiodic]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_re]))
      (add norm 0 (by grind only [neg_mul_eq_neg_mul]))
      (add norm 0 (by grind only [EReal.mul_inv]))
      (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_mul_iff]))
      (add norm 0 (by grind only [Quaternion.mul_star_eq_coe]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [mul_neg_one]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (linarith)

/-- Linearity of the sum: `Σ_m (f_m − c g_m) = Σ_m f_m − c Σ_m g_m`. -/
private lemma sum_sub_mul_eq {M : ℕ} (f g : Fin M → ℝ) (c : ℝ) :
    ∑ m : Fin M, (f m - c * g m) = ∑ m : Fin M, f m - c * ∑ m : Fin M, g m := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: genloop found an A′, but arguments drawn only from names in the context (`Finset.mul_sum (f := g) (a := c)`) already prove it, which is selection rather than construction; by the author's ruling it is not counted.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  by_cases hM : M = 0
  · simp [hM, Finset.sum]
  · simp_rw [sub_eq_add_neg]
    simp [Finset.sum_add_distrib, mul_sum, hM]

/-- Writing `μ·μ` as a square: `W − μ·μ = W − μ²`. -/
private lemma sub_mul_self_eq_sub_sq (W μ : ℝ) :
    W - μ * μ = W - μ ^ 2 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [Quaternion.mul_imJ]))
      (add norm 0 (by grind only [inv_mul']))
      (add norm 0 (by grind only [Quaternion.mul_re]))
      (add norm 0 (by grind only [neg_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
      (add norm 0 (by grind only [CauSeq.const_neg]))
      (add norm 0 (by grind only [Quaternion.mul_imI]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Real.arccos_neg]))
      (add norm 0 (by grind only [neg_sq]))
      (add norm 0 (by grind only [Quaternion.star_imI]))
      (add norm 0 (by grind only [Quaternion.neg_imI]))
      (add norm 0 (by grind only [Quaternion.mul_imK]))
      (add norm 0 (by grind only [neg_eq]))
      (add norm 0 (by grind only [Function.Antiperiodic]))
      (add norm 0 (by grind only [Quaternion.star_imK]))
      (add norm 0 (by grind only [div_eq_inv_mul]))
      (add norm 0 (by grind only [neg_mul_eq_mul_neg]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [WeierstrassCurve.ψ_neg]))
      (add unsafe 50% (by nlinarith [neg_mul_eq_neg_mul]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imJ]))
      (add unsafe 50% (by nlinarith [neg_div]))
      (add unsafe 50% (by nlinarith [mul_neg_one]))
      (add unsafe 50% (by nlinarith [neg_one_mul]))
      (add unsafe 50% (by nlinarith [QuaternionAlgebra.neg_imI]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imJ]))
      (add unsafe 50% (by nlinarith [Real.arctan_neg]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [sub_right_inj]
  --   (linarith)

/-- `μ_h' = Var_h`. -/
private lemma hasDerivAt_d2mu (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (h : Fin H) (s : ℝ) :
    HasDerivAt (fun s => d2mu a d h s) (d2var a d h s) s := by
  unfold d2mu
  refine (HasDerivAt.fun_sum fun m _ =>
    (hasDerivAt_d2sig hM a d h m s).mul_const (d h m)).congr_deriv ?_
  rw [Finset.sum_congr rfl fun m _ =>
    mul_sub_mul_self_expand (d2sig a d h m s) (d h m) (d2mu a d h s), sum_sub_mul_eq]
  exact sub_mul_self_eq_sub_sq _ _

/-- Rearranging the product rule: `Σ_i (∏_{j≠i} F_j)(F_i k_i) = (∏_i F_i) Σ_i k_i`. -/
private lemma sum_prod_erase_mul_eq {ι : Type*} [DecidableEq ι] (u : Finset ι) (F k : ι → ℝ) :
    ∑ i ∈ u, (∏ j ∈ u.erase i, F j) * (F i * k i) = (∏ i ∈ u, F i) * ∑ i ∈ u, k i := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← mul_assoc, Finset.prod_erase_mul _ _ hi]

/-- Logarithmic derivative of a product: `(∏ f_i)' = (∏ f_i) Σ k_i` when every factor satisfies
`f_i' = f_i k_i`. -/
private lemma hasDerivAt_prod_logderiv {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (f : ι → ℝ → ℝ) (k : ι → ℝ) (x : ℝ) (hf : ∀ i ∈ u, HasDerivAt (f i) (f i x * k i) x) :
    HasDerivAt (fun y => ∏ i ∈ u, f i y) ((∏ i ∈ u, f i x) * ∑ i ∈ u, k i) x := by
  exact (HasDerivAt.fun_finset_prod hf).congr_deriv (sum_prod_erase_mul_eq u (fun i => f i x) k)

/-- `π_A' = π_A S_A`. -/
private lemma hasDerivAt_d2pi (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (A : Arm H M) (s : ℝ) :
    HasDerivAt (fun s => d2pi a d A s) (d2pi a d A s * d2S a d A s) s := by
  exact hasDerivAt_prod_logderiv Finset.univ (fun h s => d2sig a d h (A h) s)
    (fun h => d h (A h) - d2mu a d h s) s fun h _ => hasDerivAt_d2sig hM a d h (A h) s

/-- `S_A' = −Σ_h Var_h`. -/
private lemma hasDerivAt_d2S (hM : 0 < M) (a d : Fin H → Fin M → ℝ) (A : Arm H M) (s : ℝ) :
    HasDerivAt (fun s => d2S a d A s) (-∑ h : Fin H, d2var a d h s) s := by
  unfold d2S
  refine (HasDerivAt.fun_sum fun h _ =>
    (hasDerivAt_d2mu hM a d h s).const_sub (d h (A h))).congr_deriv ?_
  exact Finset.sum_neg_distrib _

/-! #### Back to `provingProb` and `‖δ‖` -/

private lemma provingProb_line (Astar : Finset (Arm H M)) (l δ : Logits H M) (s : ℝ) :
    provingProb Astar (l + s • δ) =
      ∑ A ∈ Astar, d2pi (fun h m => l (h, m)) (fun h m => δ (h, m)) A s := by
  simp only [provingProb, policy, softmax, d2pi, d2sig, d2E, d2Z, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul]

/-- The squared Euclidean norm is the double sum of the squared coordinates:
`‖δ‖² = Σ_h Σ_m δ_{h,m}²`. -/
private lemma norm_sq_eq_sum_sum_sq {H M : ℕ} (δ : EuclideanSpace ℝ (Fin H × Fin M)) :
    ‖δ‖ ^ 2 = ∑ h : Fin H, ∑ m : Fin M, δ (h, m) ^ 2 := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [EuclideanSpace.norm_sq_eq, ← Fintype.sum_prod_type']
  simp [sq_abs]

/-- Rearranging the product rule: `π S · S + π (−V) = π (S² − V)`. -/
private lemma mul_mul_add_mul_neg_eq (p S V : ℝ) :
    p * S * S + p * -V = p * (S ^ 2 - V) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 512
      useDefaultSimpSet := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imJ]))
      (add norm 0 (by grind only [Quaternion.mul_re]))
      (add norm 0 (by grind only [Quaternion.mul_imK]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imI]))
      (add norm 0 (by grind only [CauSeq.const_neg]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_imK]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [neg_mul]))
      (add unsafe 50% (by nlinarith [Quaternion.mul_imJ]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [div_eq_mul_inv]))
      (add unsafe 50% (by nlinarith [Quaternion.mul_imI]))
      (add unsafe 50% (by nlinarith [mul_neg_one]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imJ]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imI]))
      (add unsafe 50% (by nlinarith [neg_one_mul]))
      (add unsafe 50% (by nlinarith [neg_mul_eq_neg_mul]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imI]))
      (add unsafe 50% (by nlinarith [inv_mul']))
      (add unsafe 50% (by nlinarith [QuaternionAlgebra.neg_imI]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imK]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imJ]))
      (add unsafe 50% (by nlinarith [Complex.I_mul_I]))
      (add unsafe 50% (by nlinarith [inv_div]))
      (add unsafe 50% (by nlinarith [neg_eq]))
      (add unsafe 50% (by nlinarith [neg_div]))
      (add unsafe 50% (by nlinarith [neg_mul_neg]))
      (add unsafe 50% (by nlinarith [WeierstrassCurve.ψ_neg]))
      (add unsafe 50% (by nlinarith [QuaternionAlgebra.neg_imJ]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imK]))
      (add unsafe 50% (by nlinarith [Complex.I_sq]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (linarith)

/-- The constant is nonnegative: `(4H + 1) Σ_h Σ_m d_{h,m}² ≥ 0`. -/
private lemma four_mul_add_one_mul_sum_sq_nonneg {M : ℕ} (H : ℕ) (d : Fin H → Fin M → ℝ) :
    0 ≤ (4 * (H : ℝ) + 1) * ∑ h : Fin H, ∑ m : Fin M, d h m ^ 2 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 100 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [Finset.one_le_prod']))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Finset.prod_nonneg]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [Finset.one_le_prod'']))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [ProbabilityTheory.truncation_nonneg]))
      (add norm 0 (by grind only [Nat.cast_nonneg]))
      (add norm 0 (by grind only [Real.rpow_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [ProbabilityTheory.variance_nonneg]))
      (add norm 0 (by grind only [unitInterval.nonneg]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [pow_le_pow_left]))
      (add norm 0 (by grind only [MeasureTheory.setIntegral_nonneg]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
      (add norm 0 (by grind only [MeasureTheory.integral_nonneg]))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [ProbabilityTheory.variance_le_expectation_sq]))
      (add norm 0 (by grind only [intervalIntegral.integral_nonneg]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [smul_nonneg]))
      (add norm 0 (by grind only [ExistsContDiffBumpBase.u_nonneg]))
      (add norm 0 (by grind only [mul_self_nonneg]))
      (add norm 0 (by grind only [one_le_tprod]))
      (add norm 0 (by grind only [BoxIntegral.integral_nonneg]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (positivity)

/-- The bound for each arm: `|S² − V| ≤ (4H + 1) D` when `S² ≤ 4HD` and `0 ≤ V ≤ D`. -/
private lemma abs_sq_sub_le_of_bounds (S V D H : ℝ) (hS : S ^ 2 ≤ 4 * H * D) (hV0 : 0 ≤ V)
    (hV1 : V ≤ D) :
    |S ^ 2 - V| ≤ (4 * H + 1) * D := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 2 round(s) and 16 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  refine' abs_sub_le_iff.2 ⟨_, _⟩
  · nlinarith [hV1, hS]
  · nlinarith [sq_nonneg (S ^ 2 - V), hV1]

/-- A nonnegative coefficient times a bounded quantity: `|p X| ≤ p K` when `p ≥ 0` and
`|X| ≤ K`. -/
private lemma abs_mul_le_mul_of_nonneg_of_abs_le (p X K : ℝ) (hp : 0 ≤ p) (hX : |X| ≤ K) :
    |p * X| ≤ p * K := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [abs_mul]
  bound [abs_of_nonneg hp]

/-- Weights summing to at most 1: `Σ_i p_i K ≤ K` when `Σ_i p_i ≤ 1` and `K ≥ 0`. -/
private lemma sum_mul_le_of_sum_le_one {ι : Type*} (s : Finset ι) (p : ι → ℝ) (K : ℝ)
    (hp : ∑ i ∈ s, p i ≤ 1) (hK : 0 ≤ K) :
    ∑ i ∈ s, p i * K ≤ K := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [← Finset.sum_mul]
  exact mul_le_of_le_one_left hK hp

/-- The "bounded Hessian" in the thesis proof (the `‖∇²_l p_s(ξ)‖₂` term): along any direction
`δ`, the second derivative of `t ↦ p_s(l + t δ)` (i.e., `δᵀ ∇²_l p_s(l + t δ) δ`) is at most
`(4H + 1) ‖δ‖²` in absolute value. The Hessian is symmetric, so this is equivalent to
`‖∇²_l p_s‖₂ ≤ 4H + 1`. `4H + 1` is a rough constant that is easy to prove, not the optimal
constant; the step-size bounds `α₀ = 1 / ((4H + 1) Δ_r)` of `growth`, `plateau`, and
`plateau_uniform` use the same constant, so a change must be made in all four places. -/
theorem provingProb_deriv2_bound (hM : 0 < M) (Astar : Finset (Arm H M)) (l δ : Logits H M)
    (t : ℝ) :
    |deriv (deriv fun s : ℝ => provingProb Astar (l + s • δ)) t| ≤ (4 * H + 1) * ‖δ‖ ^ 2 := by
  set a : Fin H → Fin M → ℝ := fun h m => l (h, m) with ha
  set d : Fin H → Fin M → ℝ := fun h m => δ (h, m) with hd
  -- `p_s(l + s δ) = Σ_{A∈𝒜*} π_A(s)`
  have hline : (fun s : ℝ => provingProb Astar (l + s • δ)) = fun s => ∑ A ∈ Astar, d2pi a d A s := by
    funext s
    exact provingProb_line Astar l δ s
  -- First derivative `Σ π_A S_A`
  have h1 : ∀ s : ℝ, HasDerivAt (fun s => ∑ A ∈ Astar, d2pi a d A s)
      (∑ A ∈ Astar, d2pi a d A s * d2S a d A s) s :=
    fun s => HasDerivAt.fun_sum fun A _ => hasDerivAt_d2pi hM a d A s
  -- Second derivative `Σ π_A (S_A² − Σ_h Var_h)`
  have h2 : HasDerivAt (fun s => ∑ A ∈ Astar, d2pi a d A s * d2S a d A s)
      (∑ A ∈ Astar, d2pi a d A t * (d2S a d A t ^ 2 - ∑ h : Fin H, d2var a d h t)) t := by
    refine HasDerivAt.fun_sum fun A _ => ?_
    exact ((hasDerivAt_d2pi hM a d A t).fun_mul (hasDerivAt_d2S hM a d A t)).congr_deriv
      (mul_mul_add_mul_neg_eq _ _ _)
  have hderiv : deriv (fun s : ℝ => provingProb Astar (l + s • δ)) =
      fun s => ∑ A ∈ Astar, d2pi a d A s * d2S a d A s := by
    rw [hline]
    funext s
    exact (h1 s).deriv
  rw [hderiv, h2.deriv]
  -- Bound: `|S_A² − Σ_h Var_h| ≤ (4H + 1) ‖δ‖²`, then use `Σ_{A∈𝒜*} π_A ≤ 1`
  set D : ℝ := ∑ h : Fin H, ∑ m : Fin M, d h m ^ 2 with hD
  have hnorm : ‖δ‖ ^ 2 = D := norm_sq_eq_sum_sum_sq δ
  have hK0 : 0 ≤ (4 * (H : ℝ) + 1) * D := four_mul_add_one_mul_sum_sq_nonneg H d
  have hA : ∀ A : Arm H M, |d2S a d A t ^ 2 - ∑ h : Fin H, d2var a d h t| ≤ (4 * H + 1) * D :=
    fun A => abs_sq_sub_le_of_bounds _ _ _ _ (d2S_sq_le hM a d A t)
      (Finset.sum_nonneg fun h _ => d2var_nonneg hM a d h t)
      (Finset.sum_le_sum fun h _ => d2var_le hM a d h t)
  have hpi0 : ∀ A : Arm H M, 0 ≤ d2pi a d A t := fun A => d2pi_nonneg hM a d A t
  calc |∑ A ∈ Astar, d2pi a d A t * (d2S a d A t ^ 2 - ∑ h : Fin H, d2var a d h t)|
      ≤ ∑ A ∈ Astar, |d2pi a d A t * (d2S a d A t ^ 2 - ∑ h : Fin H, d2var a d h t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A ∈ Astar, d2pi a d A t * ((4 * H + 1) * D) :=
        Finset.sum_le_sum fun A _ => abs_mul_le_mul_of_nonneg_of_abs_le _ _ _ (hpi0 A) (hA A)
    _ ≤ (4 * H + 1) * D :=
        sum_mul_le_of_sum_le_one Astar _ _ (d2sum_pi_le_one hM a d Astar t) hK0
    _ = (4 * H + 1) * ‖δ‖ ^ 2 := by rw [hnorm]

/-! ## Auxiliary lemmas for `growth` (the steps of the proof of Lemma 2.4 in the thesis) -/

/-- The softmax denominator is always positive: `Σ_m e^{x_m} > 0` when `M ≥ 1`. -/
private lemma exp_coord_sum_pos (M : ℕ) (hM : 0 < M) (x : Fin M → ℝ) :
    0 < ∑ m : Fin M, Real.exp (x m) := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  exact Finset.sum_pos (fun m _ => Real.exp_pos (x m)) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hM⟩⟩)

/-- `p_s` is `C^n` in the logits: it is built from finite sums and products of the softmax (the
denominator `Σ_{m'} e^{l_h^{m'}} > 0` needs `M ≥ 1`).
This guarantees that the first derivative of `t ↦ p_s(l + t δ)` is differentiable, so the
`deriv (deriv ·)` in `provingProb_deriv2_bound` is a true second derivative. -/
private lemma contDiff_provingProb (hM : 0 < M) (Astar : Finset (Arm H M)) {n : WithTop ℕ∞} :
    ContDiff ℝ n (provingProb Astar) := by
  have hsm : ∀ (h : Fin H) (m : Fin M), ContDiff ℝ n (fun l : Logits H M => softmax l h m) := by
    intro h m
    have hnum : ContDiff ℝ n (fun l : Logits H M => Real.exp (l (h, m))) :=
      Real.contDiff_exp.comp (contDiff_piLp_apply 2)
    have hden : ContDiff ℝ n (fun l : Logits H M => ∑ m' : Fin M, Real.exp (l (h, m'))) :=
      ContDiff.sum fun m' _ => Real.contDiff_exp.comp (contDiff_piLp_apply 2)
    have hne : ∀ l : Logits H M, ∑ m' : Fin M, Real.exp (l (h, m')) ≠ 0 := fun l =>
      (exp_coord_sum_pos M hM (fun m' => l (h, m'))).ne'
    exact hnum.div hden hne
  have hpol : ∀ A : Arm H M, ContDiff ℝ n (fun l : Logits H M => policy l A) := fun A =>
    contDiff_prod fun h _ => hsm h (A h)
  exact ContDiff.sum fun A _ => hpol A

/-- Along the line, `t ↦ p_s(l + t δ)` is `C²`. -/
private lemma contDiff_line (hM : 0 < M) (Astar : Finset (Arm H M)) (l δ : Logits H M) :
    ContDiff ℝ 2 (fun s : ℝ => provingProb Astar (l + s • δ)) :=
  (contDiff_provingProb hM Astar).comp (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- The line `s ↦ x + s v` has derivative `v` at every point. -/
private lemma hasDerivAt_const_add_smul_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • v) v t := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  simp_rw [add_comm x]
  have h := hasDerivAt_id t
  simpa using h.smul_const v |>.add_const x

/-- Chain rule: the derivative of `g(t) = p_s(l + t δ)` is `⟪∇_l p_s(l + t δ), δ⟫`. -/
private lemma hasDerivAt_line (Astar : Finset (Arm H M)) (l δ : Logits H M) (t : ℝ) :
    HasDerivAt (fun s : ℝ => provingProb Astar (l + s • δ))
      (inner ℝ (gradient (provingProb Astar) (l + t • δ)) δ) t := by
  have h1 : HasFDerivAt (provingProb Astar)
      (InnerProductSpace.toDual ℝ (Logits H M) (gradient (provingProb Astar) (l + t • δ)))
      (l + t • δ) :=
    ((differentiable_provingProb Astar) (l + t • δ)).hasGradientAt.hasFDerivAt
  exact h1.comp_hasDerivAt t (hasDerivAt_const_add_smul_line l δ t)

/-- The Lipschitz factor on `[0, 1]`: `B (t − 0) ≤ B` when `0 ≤ B` and `t ≤ 1`. -/
private lemma mul_sub_zero_le_of_le_one (B t : ℝ) (hB : 0 ≤ B) (h1 : t ≤ 1) :
    B * (t - 0) ≤ B := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
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
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [div_le_one']))
      (add norm 0 (by grind only [div_le_self_iff]))
      (add norm 0 (by grind only [Real.arcsin_nonneg]))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [mabs_of_one_le]))
      (add norm 0 (by grind only [zero_le_one]))
      (add norm 0 (by grind only [Real.log_nonneg]))
      (add norm 0 (by grind only [abs_eq_self]))
      (add norm 0 (by grind only [div_le_one]))
      (add norm 0 (by grind only [Nat.cast_nonneg]))
      (add norm 0 (by grind only [Real.rpow_nonneg]))
      (add norm 0 (by grind only [Real.sin_nonneg_of_nonneg_of_le_pi]))
      (add norm 0 (by grind only [Real.exp_le_one_iff]))
      (add norm 0 (by grind only [unitInterval.nonneg]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [CircleDeg1Lift.le_translationNumber_of_add_le]))
      (add norm 0 (by grind only [Real.pi_nonneg]))
      (add norm 0 (by grind only [Real.volume_Icc]))
      (add norm 0 (by grind only [Real.two_div_pi_mul_le_sin]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [Real.sin_nonneg_of_mem_Icc]))
      (add norm 0 (by grind only [one_le_oneLePart]))
      (add norm 0 (by grind only [EReal.coe_nonneg]))
      (add norm 0 (by grind only [mabs_of_le_one]))
      (add norm 0 (by grind only [le_mul_iff_one_le_right']))
      (add norm 0 (by grind only [mul_nonpos_of_nonpos_of_nonneg]))
      (add norm 0 (by grind only [Real.log_nonpos]))
      (add unsafe 10% (by grind only [le_total]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 10% (by grind only [le_of_lt]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [sub_zero]
  --   (nlinarith)

/-- Simplifying `φ(1) − φ(0)` (with `φ(t) = g(t) − t c`):
`(g₁ − 1·c) − (g₀ − 0·c) = g₁ − g₀ − c`. -/
private lemma sub_one_mul_sub_sub_zero_mul (g₁ g₀ c : ℝ) :
    g₁ - 1 * c - (g₀ - 0 * c) = g₁ - g₀ - c := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 600
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
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
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
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
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [zero_div]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [div_zero]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [WeakFEPair.Λ]))
      (add norm 0 (by grind only [tsub_div]))
      (add norm 0 (by grind only [WeakFEPair.functional_equation]))
      (add norm 0 (by grind only [div_sub_div_same]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [birkhoffSum_apply_sub_birkhoffSum]))
      (add norm 0 (by grind only [MulZeroClass]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [SubgroupClass.coe_div]))
      (add norm 0 (by grind only [div_sub']))
      (add norm 0 (by grind only [Rel.edgeDensity]))
      (add norm 0 (by grind only [neg_div]))
      (add safe 0 (by simp only [sub_div] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [div_div] at *))
      (add safe 1 (by apply div_mul))
      (add safe 0 (by simp only [mul_div] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
      (add safe 0 (by simp only [div_right_comm] at *))
      (add safe 0 (by simp only [add_div] at *))
      (add safe 0 (by simp only [div_mul_cancel₀] at *))
      (add safe 0 (by simp only [Real.div_rpow] at *))
      (add safe 0 (by simp only [eq_div_iff] at *))
      (add safe 0 (by simp only [intervalIntegral.integral_div] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring)

/-- The second-order remainder estimate in real-variable form (without the `1/2`): if `g` and
`g'` are differentiable and `|g''| ≤ B`, then `|g(1) − g(0) − g'(0)| ≤ B`. Proof: apply the mean
value inequality to `g'` to get `‖g'(t) − g'(0)‖ ≤ B` on `[0, 1]`, then apply it once more to
`φ(t) = g(t) − t g'(0)` on `[0, 1]`. -/
private lemma taylor_bound_real (g : ℝ → ℝ) (B : ℝ) (hg : Differentiable ℝ g)
    (hdd : Differentiable ℝ (deriv g)) (hB : ∀ t, |deriv (deriv g) t| ≤ B) :
    |g 1 - g 0 - deriv g 0| ≤ B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  -- Mean value inequality (`|g''| ≤ B`): `‖g'(t) − g'(0)‖ ≤ B (t − 0)` on `[0, 1]`
  have hlip : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv g t - deriv g 0‖ ≤ B * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun x _ => (hdd x).hasDerivAt.hasDerivWithinAt)
      (fun x _ => hB x)
  -- The derivative of `φ(t) = g(t) − t g'(0)` is `g'(t) − g'(0)`
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => g s - s * deriv g 0) (deriv g t - deriv g 0) (Set.Icc 0 1) t :=
    fun t _ => ((hg t).hasDerivAt.sub (hasDerivAt_mul_const (deriv g 0))).hasDerivWithinAt
  -- `‖φ'(t)‖ = ‖g'(t) − g'(0)‖ ≤ B` on `[0, 1)`
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖deriv g t - deriv g 0‖ ≤ B := fun t ht =>
    (hlip t (Set.Ico_subset_Icc_self ht)).trans (mul_sub_zero_le_of_le_one B t hB0 ht.2.le)
  -- Apply the mean value inequality to `φ` on `[0, 1]`
  have hmain : ‖g 1 - 1 * deriv g 0 - (g 0 - 0 * deriv g 0)‖ ≤ B :=
    norm_image_sub_le_of_norm_deriv_le_segment_01' hφ hbound
  rw [sub_one_mul_sub_sub_zero_mul] at hmain
  exact hmain

/-- The point of the line at `s = 1`: `x + 1·v = x + v`. -/
private lemma add_one_smul_eq_add {E : Type*} [AddCommGroup E] [Module ℝ E] (x v : E) :
    x + (1 : ℝ) • v = x + v := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
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
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [smul_add]))
      (add norm 0 (by grind only [one_smul]))
      (add norm 0 (by grind only [smul_smul]))
      (add norm 0 (by grind only [add_smul]))
      (add norm 0 (by grind only [sub_smul]))
      (add norm 0 (by grind only [MulAction]))
      (add norm 0 (by grind only [smul_sub]))
      (add norm 0 (by grind only [two_smul]))
      (add norm 0 (by grind only [smul_neg]))
      (add norm 0 (by grind only [WeakFEPair.Λ₀_eq]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_add]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_mul]))
      (add norm 0 (by grind only [neg_smul]))
      (add norm 0 (by grind only [SMulCommClass]))
      (add norm 0 (by grind only [smul_assoc]))
      (add norm 0 (by grind only [Derivation.leibniz]))
      (add norm 0 (by grind only [imaginaryPart_I_smul]))
      (add norm 0 (by grind only [TrivSqZeroExt.fst_add]))
      (add norm 0 (by grind only [Complex.coe_smul]))
      (add norm 0 (by grind only [EuclideanGeometry.reflection_vadd_smul_vsub_orthogonalProjection]))
      (add norm 0 (by grind only [lie_smul]))
      (add norm 0 (by grind only [realPart_I_smul]))
      (add norm 0 (by grind only [vsub_vadd_eq_vsub_sub]))
      (add norm 0 (by grind only [LieModule.coe_chainTop]))
      (add norm 0 (by grind only [TensorProduct.smul_add]))
      (add norm 0 (by grind only [skewAdjointPart]))
      (add norm 0 (by grind only [smul_lie]))
      (add norm 0 (by grind only [Convex.add_smul]))
      (add norm 0 (by grind only [Module.reflection_apply]))
      (add norm 0 (by grind only [TrivSqZeroExt.inr_smul]))
      (add norm 0 (by grind only [real_inner_smul_left]))
      (add norm 0 (by grind only [vsub_eq_sub]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (bound)

/-- The point of the line at `s = 0`: `x + 0·v = x`. -/
private lemma add_zero_smul_eq_self {E : Type*} [AddCommGroup E] [Module ℝ E] (x v : E) :
    x + (0 : ℝ) • v = x := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
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
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [one_smul]))
      (add norm 0 (by grind only [smul_zero]))
      (add norm 0 (by grind only [zero_smul]))
      (add norm 0 (by grind only [TrivSqZeroExt.exp_def]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_add]))
      (add norm 0 (by grind only [smul_smul]))
      (add norm 0 (by grind only [TrivSqZeroExt.exp_inr]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_inr]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_mul]))
      (add norm 0 (by grind only [smul_add]))
      (add norm 0 (by grind only [CliffordAlgebraComplex.ofComplex_I]))
      (add norm 0 (by grind only [TrivSqZeroExt.inr_smul]))
      (add norm 0 (by grind only [TrivSqZeroExt.inl_fst_add_inr_snd_eq]))
      (add norm 0 (by grind only [smul_eq_mul]))
      (add norm 0 (by grind only [NormedSpace.exp_zero]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_inl]))
      (add norm 0 (by grind only [Derivation.leibniz]))
      (add norm 0 (by grind only [TrivSqZeroExt.fst_inl]))
      (add norm 0 (by grind only [Algebra.id.smul_eq_mul]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [TrivSqZeroExt.fst_inr]))
      (add norm 0 (by grind only [TrivSqZeroExt.fst_add]))
      (add norm 0 (by grind only [add_smul]))
      (add norm 0 (by grind only [TrivSqZeroExt.fst]))
      (add norm 0 (by grind only [TrivSqZeroExt.exp_def_of_smul_comm]))
      (add norm 0 (by grind only [MulAction]))
      (add norm 0 (by grind only [IsLprojection.mul_compl_self]))
      (add norm 0 (by grind only [one_mul]))
      (add norm 0 (by grind only [IsLprojection.coe_compl]))
      (add norm 0 (by grind only [smul_sub]))
      (add norm 0 (by grind only [DualNumber.snd_eps]))
      (add norm 0 (by grind only [IsLprojection]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (bound)

/-- The second-order remainder estimate (without the `1/2`) for Eqs. (taylor_1)→(hessian_2) of
the thesis: `|p_s(l + δ) − p_s(l) − ⟪∇_l p_s(l), δ⟫| ≤ (4H + 1) ‖δ‖²`.
Proof: apply `taylor_bound_real` to `g(t) = p_s(l + t δ)`; the bound on `|g''|` is
`provingProb_deriv2_bound`, and `g'(0)` comes from the chain rule `hasDerivAt_line`. -/
private lemma taylor_bound (hM : 0 < M) (Astar : Finset (Arm H M)) (l δ : Logits H M) :
    |provingProb Astar (l + δ) - provingProb Astar l -
        inner ℝ (gradient (provingProb Astar) l) δ| ≤ (4 * H + 1) * ‖δ‖ ^ 2 := by
  have h : |provingProb Astar (l + (1 : ℝ) • δ) - provingProb Astar (l + (0 : ℝ) • δ) -
      deriv (fun s : ℝ => provingProb Astar (l + s • δ)) 0| ≤ (4 * H + 1) * ‖δ‖ ^ 2 :=
    taylor_bound_real (fun s : ℝ => provingProb Astar (l + s • δ)) _
      (fun t => (hasDerivAt_line Astar l δ t).differentiableAt)
      (contDiff_line hM Astar l δ).differentiable_deriv_two
      (provingProb_deriv2_bound hM Astar l δ)
  rw [(hasDerivAt_line Astar l δ 0).deriv, add_one_smul_eq_add, add_zero_smul_eq_self] at h
  exact h

/-- Taking `r_success = 1` and `r_failure = 0`: `(1 − 0) v = v`. -/
private lemma one_sub_zero_smul_eq {E : Type*} [AddCommGroup E] [Module ℝ E] (v : E) :
    ((1 : ℝ) - 0) • v = v := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
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
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [one_smul]))
      (add norm 0 (by grind only [sub_smul]))
      (add norm 0 (by grind only [zero_smul]))
      (add norm 0 (by grind only [WeakFEPair.Λ]))
      (add norm 0 (by grind only [smul_sub]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [smul_zero]))
      (add norm 0 (by grind only [sub_smul_slope]))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [vsub_eq_sub]))
      (add norm 0 (by grind only [smul_smul]))
      (add norm 0 (by grind only [IsLprojection]))
      (add norm 0 (by grind only [smul_add]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_one]))
      (add norm 0 (by grind only [WeakFEPair.Λ₀_eq]))
      (add norm 0 (by grind only [add_smul]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_inr]))
      (add norm 0 (by grind only [sub_div_sub_smul_slope_add_sub_div_sub_smul_slope]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_mul]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [IsLprojection.coe_compl]))
      (add norm 0 (by grind only [circleIntegral.integral_sub]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_sub]))
      (add norm 0 (by grind only [WeakFEPair.functional_equation]))
      (add norm 0 (by grind only [NormedSpace.exp_zero]))
      (add norm 0 (by grind only [Finset.sum_smul]))
      (add norm 0 (by grind only [vsub_self]))
      (add norm 0 (by grind only [WeakFEPair.functional_equation₀]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_inv]))
      (add norm 0 (by grind only [MulAction]))
      (add norm 0 (by grind only [two_smul]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_add]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (bound)

/-- Taking `r_success = 1` and `r_failure = 0`: `s (1 − 0) p = s p`. -/
private lemma mul_one_sub_zero_mul_eq (s p : ℝ) :
    s * (1 - 0) * p = s * p := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [div_one]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [mul_one]))
      (add norm 0 (by grind only [one_mul]))
      (add norm 0 (by grind only [div_self']))
      (add norm 0 (by grind only [integral_one]))
      (add norm 0 (by grind only [IsLprojection.coe_compl]))
      (add norm 0 (by grind only [zero_div]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [mul_div_cancel_left]))
      (add norm 0 (by grind only [Real.Gamma_one]))
      (add norm 0 (by grind only [mul_div_cancel]))
      (add norm 0 (by grind only [IsLprojection.mul_compl_self]))
      (add norm 0 (by grind only [gronwallBound_ε0]))
      (add norm 0 (by grind only [Real.rpow_sub_one]))
      (add norm 0 (by grind only [MulZeroClass]))
      (add norm 0 (by grind only [Real.rpow_zero]))
      (add norm 0 (by grind only [Real.rpow_sub]))
      (add norm 0 (by grind only [Real.log_one]))
      (add norm 0 (by grind only [intervalIntegral.integral_const]))
      (add norm 0 (by grind only [neg_div]))
      (add norm 0 (by grind only [Real.rpow_neg_one]))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by grind only [inner_]))
      (add norm 0 (by grind only [mellin]))
      (add norm 0 (by grind only [Real.rpow_one]))
      (add norm 0 (by grind only [Real.arccos_zero]))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [sub_div] at *))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [div_eq_one]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (linarith)

/-- A product of natural numbers cast to reals is nonnegative: `0 ≤ HM`. -/
private lemma natCast_mul_natCast_nonneg (H M : ℕ) :
    (0 : ℝ) ≤ (H : ℝ) * M := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add norm 0 (by grind only [MulZeroClass]))
      (add norm 0 (by grind only [Nat.cast_le]))
      (add norm 0 (by grind only [Nat.cast_zero]))
      (add norm 0 (by grind only [ArithmeticFunction.vonMangoldt_nonneg]))
      (add norm 0 (by grind only [FractionalIdeal.count_coe_nonneg]))
      (add norm 0 (by grind only [FractionalIdeal.zero_le]))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [le_mul_iff_one_le_right']))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [Poly.sumsq_nonneg]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [one_le]))
      (add norm 0 (by grind only [le_mul_iff_one_le_left']))
      (add norm 0 (by grind only [zero_le']))
      (add norm 0 (by grind only [le_trans]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [Ordinal.natCast_le]))
      (add norm 0 (by grind only [mul_nonpos_of_nonpos_of_nonneg]))
      (add norm 0 (by rw [ZMod.natCast_self]))
      (add unsafe 10% (by grind only [Nat.cast_nonneg]))
      (add unsafe 10% (by grind only [Num.cast_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 10% (by grind only [Nat.cast_lt]))
      (add unsafe 10% (by grind only [Nat.zero_le]))
      (add unsafe 10% (by grind only [Int.ofNat_le]))
      (add unsafe 50% (by nlinarith [Nat.cast_pos]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₄]))
      (add unsafe 10% (by grind only [SzemerediRegularity.seven_le_initialBound]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (nlinarith)

/-- Squaring removes the square root: `(√K · p)² = K p²` when `K ≥ 0`. -/
private lemma sqrt_mul_sq_eq_mul_sq (K p : ℝ) (hK : 0 ≤ K) :
    (Real.sqrt K * p) ^ 2 = K * p ^ 2 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
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
      (add unsafe 50% (by ring_nf at *))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [sq_abs]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add norm 0 (by grind only [sq_sub_sq]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [Real.sqrt_sq_eq_abs]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [Real.mul_self_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_mul']))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Quaternion.normSq_coe]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [RCLike.normSq_eq_def']))
      (add norm 0 (by grind only [WithLp.prod_norm_sq_eq_of_L2]))
      (add norm 0 (by grind only [Quaternion.normSq_ratCast]))
      (add norm 0 (by grind only [norm_add_sq_real]))
      (add norm 0 (by grind only [Quaternion.inner_self]))
      (add norm 0 (by grind only [sq_lt_sq]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 0 (by grind only [Real.sqrt_mul_self]))
      (add norm 0 (by grind only [Real.sqrt]))
      (add norm 0 (by grind only [PiLp.norm_eq_of_L2]))
      (add norm 0 (by grind only [Quaternion.sq_eq_normSq]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_coe_center_sq]))
      (add norm 0 (by grind only [Complex.sq_abs]))
      (add unsafe 90% (by simp only [Real.rpow_two] at *))
      (add unsafe 50% (by simp only [sq_add_sq_mul]))
      (add unsafe 90% (by simp only [pow_two] at *))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   simp_all only [Real.sq_sqrt]
  --   (linarith)

/-- Lemma 2.3 with `rs = 1` and `rf = 0` (then `J_sparse = p_s`): `‖∇_l p_s‖² ≤ HM · p_s²`. -/
private lemma norm_gradient_provingProb_sq_le (hM : 0 < M) (Astar : Finset (Arm H M))
    (l : Logits H M) :
    ‖gradient (provingProb Astar) l‖ ^ 2 ≤ (H : ℝ) * M * provingProb Astar l ^ 2 := by
  have h1 := norm_gradient_expectedReward_le Astar 1 0 zero_lt_one l
  rw [gradient_expectedReward hM Astar 1 0 l, one_sub_zero_smul_eq, mul_one_sub_zero_mul_eq] at h1
  calc ‖gradient (provingProb Astar) l‖ ^ 2
      ≤ (Real.sqrt ((H : ℝ) * M) * provingProb Astar l) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (H : ℝ) * M * provingProb Astar l ^ 2 :=
        sqrt_mul_sq_eq_mul_sq ((H : ℝ) * M) (provingProb Astar l) (natCast_mul_natCast_nonneg H M)

/-- The step-size condition: `L(αΔ) ≤ 1` when `0 < L`, `0 < Δ`, and `α ≤ 1/(LΔ)`. -/
private lemma mul_mul_le_one_of_le_one_div (α Δ L : ℝ) (hΔ : 0 < Δ) (hL : 0 < L)
    (hαL : α ≤ 1 / (L * Δ)) :
    L * (α * Δ) ≤ 1 := by
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
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [mul_div_cancel₀]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le']))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (field_simp [*] at *)
  --   (linarith)

/-- For a small step size, the first-order term dominates the second-order term:
`L a² G ≤ aG` when `0 ≤ aG` and `La ≤ 1`. -/
private lemma mul_sq_mul_le_of_mul_le_one (a G L : ℝ) (haG : 0 ≤ a * G) (hLa : L * a ≤ 1) :
    L * (a ^ 2 * G) ≤ a * G := by
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
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [mul_le_of_le_one_left]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [Real.pi_nonneg]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [pow_le_pow_left]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [norm_jacobiTheta₂_term_le]))
      (add norm 0 (by grind only [ProbabilityTheory.mgf_nonneg]))
      (add norm 0 (by grind only [unitInterval.nonneg]))
      (add norm 0 (by grind only [Real.rpow_nonneg]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [real_inner_le_norm]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [inv_nonneg]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (nlinarith)

/-- The lower bound: `0 ≤ D` when `D − aG ≥ −L a² G` and `L a² G ≤ aG`. -/
private lemma nonneg_of_neg_le_sub_of_le (a G L D : ℝ) (hD1 : -(L * (a ^ 2 * G)) ≤ D - a * G)
    (hdom : L * (a ^ 2 * G) ≤ a * G) :
    0 ≤ D := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
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
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [unitInterval.nonneg]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [Real.log_nonneg]))
      (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [one_le_oneLePart]))
      (add norm 0 (by grind only [div_le_one']))
      (add norm 0 (by grind only [Real.sqrt_nonneg]))
      (add norm 0 (by grind only [div_le_self_iff]))
      (add norm 0 (by grind only [smul_nonneg]))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [one_le_leOnePart]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [mul_nonpos_of_nonpos_of_nonneg]))
      (add unsafe 50% (by nlinarith [unitInterval.le_one]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 50% (by nlinarith [CircleDeg1Lift.le_translationNumber_of_add_le]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [neg_le_sub_iff_le_add]
  --   (linarith)

/-- The upper bound: `D ≤ 2aG` when `D − aG ≤ L a² G` and `L a² G ≤ aG`. -/
private lemma le_two_mul_of_sub_le_of_le (a G L D : ℝ) (hD2 : D - a * G ≤ L * (a ^ 2 * G))
    (hdom : L * (a ^ 2 * G) ≤ a * G) :
    D ≤ 2 * (a * G) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
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
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [EisensteinSeries.r1_aux_bound]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [Real.le_sqrt']))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Int.le_self_sq]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right']))
      (add unsafe 50% (by nlinarith [mul_le_mul_left']))
      (add unsafe 50% (by nlinarith [one_add_mul_le_pow]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [tsub_le_iff_right]
  --   (linarith)

/-- Substituting `G ≤ K p²`: `2αΔG ≤ 2αKΔp²` when `0 ≤ αΔ`. -/
private lemma two_mul_mul_le_of_le_mul_sq (α Δ G K p : ℝ) (ha : 0 ≤ α * Δ)
    (hGK : G ≤ K * p ^ 2) :
    2 * (α * Δ * G) ≤ 2 * α * K * Δ * p ^ 2 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 60
      maxGoals := 512
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
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
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [mul_pow]))
      (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [Real.le_sqrt]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [pow_le_pow_left]))
      (add norm 0 (by grind only [Real.sqrt_le_left]))
      (add norm 0 (by grind only [Real.le_sqrt_of_sq_le]))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 0 (by grind only [sq_le_sq]))
      (add norm 0 (by grind only [norm_jacobiTheta₂_term_fderiv_le]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (nlinarith)

/-- The final algebra: `a = αΔ`, `G = ‖∇_l p_s‖²`, `D = p_{k+1} − p_k`. From `|D − aG| ≤ L a² G`
and `L a ≤ 1`, we get `L a² G ≤ aG` (the first-order term dominates the second-order term),
so `0 ≤ D ≤ 2aG ≤ 2aK p²` (`K = HM`). -/
private lemma growth_algebra {α Δ L G K p D : ℝ} (hα : 0 < α) (hΔ : 0 < Δ) (hL : 0 < L)
    (hαL : α ≤ 1 / (L * Δ)) (hG0 : 0 ≤ G) (hGK : G ≤ K * p ^ 2)
    (hD : |D - α * Δ * G| ≤ L * ((α * Δ) ^ 2 * G)) :
    0 ≤ D ∧ D ≤ 2 * α * K * Δ * p ^ 2 := by
  have hLa : L * (α * Δ) ≤ 1 := mul_mul_le_one_of_le_one_div α Δ L hΔ hL hαL
  have ha : 0 < α * Δ := mul_pos hα hΔ
  have hdom : L * ((α * Δ) ^ 2 * G) ≤ α * Δ * G :=
    mul_sq_mul_le_of_mul_le_one (α * Δ) G L (mul_nonneg ha.le hG0) hLa
  obtain ⟨hD1, hD2⟩ := abs_le.mp hD
  exact ⟨nonneg_of_neg_le_sub_of_le (α * Δ) G L D hD1 hdom,
    (le_two_mul_of_sub_le_of_le (α * Δ) G L D hD2 hdom).trans
      (two_mul_mul_le_of_le_mul_sq α Δ G K p ha.le hGK)⟩

/-- The constant of the Hessian bound is positive: `0 < 4H + 1`. -/
private lemma four_mul_natCast_add_one_pos (H : ℕ) :
    (0 : ℝ) < 4 * H + 1 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
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
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [one_lt_div]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [lt_mul_of_le_of_one_lt]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [lt_div_iff']))
      (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_right]))
      (add unsafe 50% (by nlinarith [div_lt_iff']))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [Nat.cast_pos]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [zero_lt_one]))
      (add unsafe 50% (by nlinarith [Real.aux₀]))
      (add unsafe 50% (by nlinarith [one_lt_gold]))
      (add unsafe 50% (by nlinarith [gold_pos]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_right]))
      (add unsafe 50% (by nlinarith [div_lt_one]))
      (add unsafe 50% (by nlinarith [Real.log_lt_sub_one_of_pos]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_right]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_le_of_lt]))
      (add unsafe 50% (by nlinarith [Real.log_lt_log_iff]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_logb_iff]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_of_le]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_right']))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (linarith)

/-- The thesis's `δ = α Δ_r ∇_l p_k`: `x + α (Δ v) = x + (αΔ) v`. -/
private lemma add_smul_smul_eq_add_mul_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (α Δ : ℝ) (x v : E) :
    x + α • (Δ • v) = x + (α * Δ) • v := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by rfl))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [smul_add]))
      (add norm 0 (by grind only [smul_smul]))
      (add norm 0 (by grind only [MulAction]))
      (add norm 0 (by grind only [add_smul]))
      (add norm 0 (by grind only [smul_eq_mul]))
      (add norm 0 (by grind only [smul_assoc]))
      (add norm 0 (by grind only [SMulCommClass]))
      (add norm 0 (by grind only [Complex.coe_smul]))
      (add norm 0 (by grind only [smul_sub]))
      (add norm 0 (by grind only [one_smul]))
      (add norm 0 (by grind only [Quaternion.mul_coe_eq_smul]))
      (add norm 0 (by grind only [real_inner_smul_left]))
      (add norm 0 (by grind only [Derivation.leibniz]))
      (add norm 0 (by grind only [Subgroup.smul_def]))
      (add norm 0 (by grind only [Quaternion.smul_coe]))
      (add norm 0 (by grind only [QuaternionAlgebra.mul_coe_eq_smul]))
      (add norm 0 (by grind only [TrivSqZeroExt.inr_smul]))
      (add norm 0 (by grind only [ContMDiffSection.coe_smul]))
      (add norm 0 (by grind only [Algebra.id.smul_eq_mul]))
      (add norm 0 (by grind only [real_inner_smul_right]))
      (add norm 0 (by grind only [sub_smul]))
      (add norm 0 (by grind only [UpperHalfPlane.coe_pos_real_smul]))
      (add norm 0 (by grind only [Quaternion.smul_imJ]))
      (add norm 0 (by grind only [two_smul]))
      (add norm 0 (by grind only [QuaternionAlgebra.Basis.k_mul_k]))
      (add norm 0 (by grind only [TrivSqZeroExt.snd_mul]))
      (add norm 0 (by grind only [imaginaryPart_I_smul]))
      (add norm 0 (by grind only [ContinuousLinearMap.coe_smul]))
      (add norm 0 (by grind only [Units.smul_def]))
      (add norm 0 (by grind only [ContinuousLinearMap.coe_smul']))
      (add norm 0 (by grind only [neg_smul]))
      (add norm 0 (by grind only [smul_neg]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (grind only [smul_smul])

/-- The first-order term: `⟪v, c v⟫ = c ‖v‖²`. -/
private lemma inner_smul_self_eq_mul_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c : ℝ) (v : E) :
    inner ℝ v (c • v) = c * ‖v‖ ^ 2 := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  trans c * inner ℝ v v
  · rw [inner_smul_right]
  · simp [inner_self_eq_norm_sq_to_K, sq]

/-- The second-order term: `‖c v‖² = c² ‖v‖²`. -/
private lemma norm_smul_sq_eq_sq_mul_norm_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (v : E) :
    ‖c • v‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Lemma 2.4: for all `0 < α ≤ α₀ = 1 / ((4H + 1) Δ_r)` and all `l`,
`l' = l + α ∇_l J_sparse(l)` satisfies `0 ≤ p_s(l') − p_s(l) ≤ c · p_s(l)²` with
`c = 2 α H M Δ_r`. -/
theorem growth (hM : 0 < M) (Astar : Finset (Arm H M)) (rs rf : ℝ) (hr : rf < rs) :
    ∀ α : ℝ, 0 < α → α ≤ 1 / ((4 * H + 1) * (rs - rf)) → ∀ l : Logits H M,
      0 ≤ provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ∧
      provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ≤
        2 * α * ((H : ℝ) * M) * (rs - rf) * provingProb Astar l ^ 2 := by
  intro α hα hαle l
  have hΔ : 0 < rs - rf := sub_pos.mpr hr
  have hL : (0 : ℝ) < 4 * H + 1 := four_mul_natCast_add_one_pos H
  -- The thesis's `δ = α ∇_l J_sparse(l_k) = α Δ_r ∇_l p_k`
  have hstep : ascentStep Astar rs rf α l =
      l + (α * (rs - rf)) • gradient (provingProb Astar) l := by
    rw [ascentStep, gradient_expectedReward hM Astar rs rf l]
    exact add_smul_smul_eq_add_mul_smul α (rs - rf) l (gradient (provingProb Astar) l)
  have htay := taylor_bound hM Astar l ((α * (rs - rf)) • gradient (provingProb Astar) l)
  rw [inner_smul_self_eq_mul_norm_sq, norm_smul_sq_eq_sq_mul_norm_sq] at htay
  rw [hstep]
  exact growth_algebra hα hΔ hL hαle (sq_nonneg _)
    (norm_gradient_provingProb_sq_le hM Astar l) htay

end Sec2

end

-- ===== project/Sec2/Plateau.lean =====
section

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
private lemma sum_exp_pos_Plateau (n : ℕ) (hn : 0 < n) (g : Fin n → ℝ) : 0 < ∑ i, Real.exp (g i) := by
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
          (sum_exp_pos_Plateau M hM fun m' => peakLogits A t (h, m')) hsum

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

end

-- ===== project/Sec2/RandomSearch.lean =====
section

/-!
# Lemma 2.7 (Random search costs Θ(1/p_s)) and Corollary 2.8 (Cost of per-context search)

Lemma 2.7 of the thesis: fix a context and a distribution `π(·∣C)` that stays fixed during the
search, with proving probability `p_s`. For any fixed `q ∈ (0,1)`, the smallest number `N` of
independent samples that yield at least one success with probability at least `q` satisfies
`N ∈ Θ(1/p_s)` (as `p_s → 0`); more precisely, `N = −log(1−q)/p_s · (1 + O(p_s))`.

User decision (2026-11-01): start from "the probability that all `N` independent samples fail is
`(1 − p_s)^N`", without formalizing the product measure; so `p` here is just the single-sample
success probability `p_s`. `N` depends on `π` only through `p_s`, so a statement that holds for
every `p` covers any fixed distribution.

The final `uniformSearch_bounds` is the last sentence of Remark 2.6 (with `p := p_s(0)`), so this
file imports `Sec2.Basic`; Lemma 2.7 and Corollary 2.8 themselves do not use the definitions in
`Sec2.Basic`.
-/

open Filter Topology Asymptotics Finset

namespace Sec2

/-- The smallest number `N` of samples such that `1 − (1 − p)^N ≥ q`. -/
noncomputable def minSamples (q p : ℝ) : ℕ :=
  sInf {N : ℕ | q ≤ 1 - (1 - p) ^ N}

/-! ### Steps of the proof of Lemma 2.7 (auxiliary lemmas)

The thesis's proof: the probability that all `N` samples fail is `(1 − p)^N`, so
`P_N = 1 − (1 − p)^N`; solving `P_N ≥ q` gives `N ≥ log(1−q)/log(1−p)`; then use
`log(1−p) = −p + O(p²)`. For the upper bound, as described in `minSamples_bounds`, take
`K = ⌈−log(1−q)/p⌉` and use `1 − p ≤ e^{−p}`; the lower bound with explicit constants uses
Bernoulli's inequality (union bound).

Each leaf lemma does a single mathematical step and uses only Mathlib; the remaining proofs only
chain them together. -/

/-- Both sides of `1 − p ≤ e^{−p}` are nonnegative (`p ≤ 1`); raising them to the power `N` gives
`(1 − p)^N ≤ (e^{−p})^N`. -/
private lemma one_sub_pow_le_exp_neg_pow (p : ℝ) (N : ℕ) (hp1 : p ≤ 1) :
    (1 - p) ^ N ≤ Real.exp (-p) ^ N := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  gcongr
  · linarith
  · linarith [Real.add_one_le_exp (-p)]

/-- Law of exponents: `(e^{−p})^N = e^{−pN}`. -/
private lemma exp_neg_pow_eq (p : ℝ) (N : ℕ) :
    Real.exp (-p) ^ N = Real.exp (-(p * N)) := by
  -- [satp + generative rule] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- The generator g (an Opus 5.5 subagent) supplies t_C = `(-p) N`; `p N` as the arguments of lemma ℓ = `Real.exp_nat_mul` in rule 17 of A.
  -- Rule type, priority, position, wrapper and ℓ are unchanged, so A′ differs from A only by t_C; arguments drawn only
  -- from names in the context do not prove the subgoal (thesis Section 5.5):
  --   A : (add norm 0 (by grind only [Real.exp_nat_mul]))
  --   A′: (add norm 0 (by grind only [Real.exp_nat_mul (-p) N, Real.exp_nat_mul p N]))
  -- Proof body: the full A′ (A is the `satp?` output, port 5171; only the rule above and indentation changed).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.exp_nat_mul (-p) N, Real.exp_nat_mul p N]))
      (add norm 0 (by grind only [Real.exp_mul]))
      (add norm 0 (by grind only [Real.exp_log]))
      (add norm 0 (by grind only [Real.exp_arsinh]))
      (add norm 0 (by grind only [Real.exp_eq_exp_ℝ]))
      (add norm 0 (by grind only [Real.log_exp]))
      (add norm 0 (by grind only [Real.exp_neg]))
      (add norm 0 (by grind only [Real.exp]))
      (add norm 0 (by grind only [NormedSpace.of_real_exp_ℝ_ℝ]))
      (add norm 0 (by grind only [Real.exp_pos]))
      (add norm 0 (by grind only [Real.exp_add]))
      (add norm 0 (by grind only [rexp_neg_deriv_aux]))
      (add norm 0 (by grind only [rexp_neg_injOn_aux]))
      (add norm 0 (by grind only [Real.exp_ne_zero]))
      (add norm 0 (by grind only [Real.rpow_def_of_pos]))
      (add norm 0 (by grind only [integral_exp]))
      (add norm 0 (by grind only [Real.exp_sub]))
      (add norm 0 (by grind only [Real.exp_log_eq_abs]))
      (add norm 0 (by rw [Quaternion.exp_coe]))
      (add norm 0 (by grind only [Real.exp_eq_exp]))
      (add norm 0 (by grind only [neg_mul]))
      (add norm 0 (by grind only [Complex.exp_nat_mul]))
      (add norm 0 (by grind only [Real.exp_half]))
      (add norm 0 (by grind only [Real.exp_one_rpow]))
      (add norm 0 (by grind only [rexp_neg_image_aux]))
      (add norm 0 (by grind only [Real.exp_le_exp]))
      (add norm 0 (by grind only [Real.exp_injective]))
      (add norm 0 (by grind only [Complex.exp_eq_exp_ℂ]))
      (add norm 0 (by grind only [Complex.ofReal_exp]))
      (add norm 0 (by grind only [NormedSpace.exp_ℝ_ℂ_eq_exp_ℂ_ℂ]))
      (add norm 0 (by grind only [Real.exp_nonneg]))
      (add norm 0 (by grind only [Real.rpow_def_of_neg]))
  -- The `aesop?` "Try this" output with A′, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (grind only [Real.exp_nat_mul (-p) N, Real.exp_nat_mul p N])

/-- For `p ≤ 1`, `(1 − p)^N ≤ e^{−pN}` (from `1 − p ≤ e^{−p}`). -/
private theorem one_sub_pow_le_exp {p : ℝ} (hp1 : p ≤ 1) (N : ℕ) :
    (1 - p) ^ N ≤ Real.exp (-(p * N)) :=
  (one_sub_pow_le_exp_neg_pow p N hp1).trans_eq (exp_neg_pow_eq p N)

/-- Multiplying both sides by `p > 0`: `−a/p ≤ x` implies `−(p·x) ≤ a`. -/
private lemma neg_mul_le_of_neg_div_le (a p x : ℝ) (hp0 : 0 < p) (h : -a / p ≤ x) :
    -(p * x) ≤ a := by
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
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [inv_mabs_le]))
      (add norm 0 (by grind only [inv_inv]))
      (add norm 0 (by grind only [Real.exp_neg]))
      (add norm 0 (by grind only [inv_le']))
      (add norm 0 (by grind only [neg_inv]))
      (add norm 0 (by grind only [AkraBazziRecurrence.GrowsPolynomially.mul]))
      (add norm 0 (by grind only [Real.arcsin_neg]))
      (add norm 0 (by grind only [inv_neg]))
      (add norm 0 (by grind only [AkraBazziRecurrence.GrowsPolynomially.iff_eventuallyEq]))
      (add unsafe 50% (by nlinarith [inv_le_inv_iff]))
      (add unsafe 50% (by nlinarith [div_eq_mul_inv]))
      (add unsafe 10% (by grind only [Real.rpow_neg]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [neg_div]))
      (add unsafe 50% (by nlinarith [neg_mul]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [inv_le]))
      (add unsafe 50% (by nlinarith [le_inv]))
      (add unsafe 50% (by nlinarith [div_neg]))
      (add unsafe 50% (by nlinarith [div_eq_inv_mul]))
      (add unsafe 50% (by nlinarith [inv_mul']))
      (add unsafe 50% (by nlinarith [inv_le_inv]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r_lower_bound_on_verticalStrip]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imJ]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imI]))
      (add unsafe 50% (by nlinarith [neg_eq]))
      (add unsafe 50% (by nlinarith [neg_mul_eq_mul_neg]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imI]))
      (add unsafe 50% (by nlinarith [Quaternion.mul_imJ]))
      (add unsafe 50% (by nlinarith [neg_mul_eq_neg_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (field_simp [*] at *)
  --   (linarith)

/-- Exponentiating: `x ≤ log(1 − q)` (`q < 1`) implies `e^x ≤ 1 − q`. -/
private lemma exp_le_one_sub_of_le_log (x q : ℝ) (hq1 : q < 1) (h : x ≤ Real.log (1 - q)) :
    Real.exp x ≤ 1 - q := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
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
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.exp_le_exp]))
      (add norm 0 (by grind only [Real.exp_pos]))
      (add norm 0 (by grind only [Real.exp_sub]))
      (add norm 0 (by grind only [Real.exp_add]))
      (add norm 0 (by grind only [Real.le_log_iff_exp_le]))
      (add norm 0 (by grind only [Real.add_one_le_exp]))
      (add norm 0 (by grind only [Real.exp]))
      (add norm 0 (by grind only [Real.log_le_iff_le_exp]))
      (add norm 0 (by grind only [Real.exp_eq_exp_ℝ]))
      (add norm 0 (by grind only [Real.exp_mul]))
      (add norm 0 (by grind only [Real.exp_log]))
      (add norm 0 (by grind only [rexp_neg_deriv_aux]))
      (add norm 0 (by grind only [integral_exp]))
      (add norm 0 (by grind only [Real.exp_nonneg]))
      (add norm 0 (by grind only [Real.exp_ne_zero]))
      (add norm 0 (by grind only [Real.log_exp]))
      (add norm 0 (by grind only [rexp_neg_injOn_aux]))
      (add norm 0 (by grind only [Real.le_exp_log]))
      (add norm 0 (by grind only [Real.exp_one_rpow]))
      (add norm 0 (by grind only [Real.exp_neg]))
      (add norm 0 (by grind only [Real.exp_le_one_iff]))
      (add norm 0 (by grind only [Real.exp_zero]))
      (add norm 0 (by grind only [Real.exp_le_exp_of_le]))
      (add norm 0 (by grind only [Real.rpow_def_of_pos]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [Real.exp_arsinh]))
      (add norm 0 (by grind only [rexp_neg_image_aux]))
      (add norm 0 (by grind only [Real.exp_injective]))
      (add norm 0 (by grind only [ProbabilityTheory.mgf_nonneg]))
      (add unsafe 50% (by nlinarith [Behrend.lower_bound_le_one]))
      (add unsafe 50% (by nlinarith [Behrend.exp_neg_two_mul_le]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (grind only [Real.le_log_iff_exp_le])

/-- Witness for the upper bound: `K = ⌈−log(1−q)/p⌉` samples already reach the threshold, since
`(1−p)^K ≤ e^{−pK} ≤ 1 − q`. -/
private theorem reaches_ceil {q p : ℝ} (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    q ≤ 1 - (1 - p) ^ ⌈-Real.log (1 - q) / p⌉₊ := by
  -- `−log(1−q)/p ≤ K` gives `−pK ≤ log(1−q)`; exponentiating gives `e^{−pK} ≤ 1 − q`
  have hK := Nat.le_ceil (-Real.log (1 - q) / p)
  have h1 := one_sub_pow_le_exp hp1 ⌈-Real.log (1 - q) / p⌉₊
  have h2 := exp_le_one_sub_of_le_log _ q hq1 (neg_mul_le_of_neg_div_le _ p _ hp0 hK)
  exact le_sub_comm.1 (h1.trans h2)

/-- `minSamples` is indeed the smallest number of samples: it reaches the threshold, and no `N` that
reaches the threshold is smaller. -/
theorem minSamples_spec {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    q ≤ 1 - (1 - p) ^ minSamples q p ∧
      ∀ N : ℕ, q ≤ 1 - (1 - p) ^ N → minSamples q p ≤ N := by
  -- The set is nonempty (`reaches_ceil`), so its `sInf` belongs to it and is a lower bound
  have hne : {N : ℕ | q ≤ 1 - (1 - p) ^ N}.Nonempty := ⟨_, reaches_ceil hq1 hp0 hp1⟩
  exact ⟨Nat.sInf_mem hne, fun N hN => Nat.sInf_le hN⟩

/-- Upper bound: `N ≤ ⌈−log(1−q)/p⌉` (`reaches_ceil` and the minimality of `N`). -/
private theorem minSamples_le_ceil {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) : minSamples q p ≤ ⌈-Real.log (1 - q) / p⌉₊ :=
  (minSamples_spec hq0 hq1 hp0 hp1).2 _ (reaches_ceil hq1 hp0 hp1)

/-- Bernoulli's inequality `(1 − p)^N ≥ 1 − pN` (`p ≤ 1`), rearranged, is the union bound
`1 − (1 − p)^N ≤ pN`. -/
private lemma one_sub_one_sub_pow_le (p : ℝ) (N : ℕ) (hp1 : p ≤ 1) :
    1 - (1 - p) ^ N ≤ p * N := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  cases' N with N
  · simp
  · induction N
    · simp
    · simp_all [pow_succ, mul_add]
      nlinarith [sq_nonneg (1 - p), sq_nonneg p]

/-- Union bound (Bernoulli's inequality `(1 − p)^N ≥ 1 − Np`): if `N` samples reach the threshold
`q`, then `q ≤ pN`. -/
private theorem le_mul_of_reaches {q p : ℝ} (hp1 : p ≤ 1) {N : ℕ}
    (hN : q ≤ 1 - (1 - p) ^ N) : q ≤ p * N :=
  hN.trans (one_sub_one_sub_pow_le p N hp1)

/-- Dividing both sides by `p > 0`: `q ≤ p·x` implies `q/p ≤ x`. -/
private lemma div_le_of_le_mul_of_pos (q p x : ℝ) (hp0 : 0 < p) (h : q ≤ p * x) :
    q / p ≤ x := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
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
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [div_le_self]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [one_sub_div]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_one))
      (add safe 0 (by nlinarith [mul_div_cancel₀]))
      (add safe 0 (by nlinarith [Real.mul_le_sin]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [ceilDiv_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (field_simp [*] at *)
  --   simp_all only

/-- Lower bound (union bound): `q/p ≤ N`. -/
private theorem div_le_minSamples {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) : q / p ≤ minSamples q p :=
  div_le_of_le_mul_of_pos q p _ hp0 (le_mul_of_reaches hp1 (minSamples_spec hq0 hq1 hp0 hp1).1)

/-- For `q ∈ (0,1)`, `−log(1−q) > 0`. -/
private lemma neg_log_one_sub_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < -Real.log (1 - q) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
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
      (add norm 0 (by grind only [Left.inv_lt_one_iff]))
      (add norm 0 (by grind only [Real.log_neg_eq_log]))
      (add norm 0 (by grind only [Right.inv_lt_one_iff]))
      (add norm 0 (by grind only [Real.log_pos_of_lt_neg_one]))
      (add norm 0 (by grind only [lt_inv']))
      (add norm 0 (by grind only [Real.log_inv]))
      (add norm 0 (by grind only [Real.sign_of_neg]))
      (add norm 0 (by grind only [Real.log_neg_of_lt_zero]))
      (add norm 0 (by grind only [EReal.neg_top]))
      (add norm 0 (by grind only [mul_neg_of_neg_of_pos]))
      (add norm 0 (by grind only [Real.rpow_logb_of_neg]))
      (add norm 0 (by grind only [inv_gold]))
      (add norm 0 (by grind only [div_neg_of_neg_of_pos]))
      (add norm 0 (by grind only [Left.one_lt_inv_iff]))
      (add unsafe 50% (by nlinarith [Real.log_neg]))
      (add unsafe 50% (by nlinarith [Real.logb_neg]))
      (add unsafe 50% (by nlinarith [Real.logb_abs]))
      (add unsafe 50% (by nlinarith [inv_lt_inv_iff]))
      (add unsafe 50% (by nlinarith [inv_lt']))
      (add unsafe 50% (by nlinarith [lt_inv]))
      (add unsafe 50% (by nlinarith [inv_lt_inv]))
      (add unsafe 50% (by nlinarith [Real.log_neg_iff]))
      (add unsafe 50% (by nlinarith [inv_lt_one]))
      (add unsafe 50% (by nlinarith [inv_lt]))
      (add unsafe 50% (by nlinarith [Real.log_pos]))
      (add unsafe 50% (by nlinarith [Real.log_div_log]))
      (add unsafe 50% (by nlinarith [mul_pos_iff]))
      (add unsafe 50% (by nlinarith [Real.b_pos]))
      (add unsafe 50% (by nlinarith [Real.rpow_lt_rpow_of_exponent_gt]))
      (add unsafe 50% (by nlinarith [Real.logb_neg_of_base_lt_one]))
      (add unsafe 50% (by nlinarith [Real.rpow_logb]))
      (add unsafe 50% (by nlinarith [Real.rpow_lt_rpow_left_iff_of_base_lt_one]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [Left.neg_pos_iff]
  --   (bound)

/-- Ceiling bound: `N ≤ ⌈L/p⌉` (`L ≥ 0`, `p > 0`) implies `N < L/p + 1`. -/
private lemma cast_lt_div_add_one_of_le_ceil (L p : ℝ) (N : ℕ) (hL : 0 ≤ L) (hp0 : 0 < p)
    (hN : N ≤ ⌈L / p⌉₊) :
    (N : ℝ) < L / p + 1 := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  have hc : ((⌈L / p⌉₊ : ℕ) : ℝ) < L / p + 1 := Nat.ceil_lt_add_one (div_nonneg hL hp0.le)
  have hN' : (N : ℝ) ≤ ((⌈L / p⌉₊ : ℕ) : ℝ) := by exact_mod_cast hN
  linarith

/-- For `0 < p ≤ 1`, `1 ≤ 1/p`, so `L/p + 1 ≤ (L + 1)/p`. -/
private lemma div_add_one_le_add_one_div (L p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    L / p + 1 ≤ (L + 1) / p := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [div_le_self]))
      (add safe 0 (by nlinarith [Real.mul_le_sin]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le']))
      (add unsafe 50% (by nlinarith [div_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [SzemerediRegularity.coe_m_add_one_pos]))
      (add unsafe 50% (by nlinarith [Behrend.two_div_one_sub_two_div_e_le_eight]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [Real.log_le_sub_one_of_pos]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [one_sub_div]))
      (add unsafe 50% (by nlinarith [one_div_le]))
      (add unsafe 50% (by nlinarith [div_le_one_of_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (field_simp [*] at *)
  --   simp_all only [add_le_add_iff_left]

/-- If `N ≤ ⌈L/p⌉` and `0 < p ≤ 1`, then `N ≤ (L + 1)/p`. -/
private theorem cast_le_div_of_le_ceil {L p : ℝ} (hL : 0 ≤ L) (hp0 : 0 < p) (hp1 : p ≤ 1) {N : ℕ}
    (hN : N ≤ ⌈L / p⌉₊) : (N : ℝ) ≤ (L + 1) / p :=
  (cast_lt_div_add_one_of_le_ceil L p N hL hp0 hN).le.trans
    (div_add_one_le_add_one_div L p hp0 hp1)

/-- Upper bound: `N ≤ (−log(1−q) + 1)/p`. -/
private theorem minSamples_le_div {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) : (minSamples q p : ℝ) ≤ (-Real.log (1 - q) + 1) / p :=
  cast_le_div_of_le_ceil (neg_log_one_sub_pos q hq0 hq1).le hp0 hp1
    (minSamples_le_ceil hq0 hq1 hp0 hp1)

/-- Taking logs of both sides: `(1 − p)^N ≤ 1 − q` (`p < 1`) implies
`N · log(1 − p) ≤ log(1 − q)`. -/
private lemma mul_log_le_log_of_pow_le (p q : ℝ) (N : ℕ) (hp1 : p < 1)
    (h : (1 - p) ^ N ≤ 1 - q) :
    N * Real.log (1 - p) ≤ Real.log (1 - q) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [← Real.log_rpow (by linarith)]
  gcongr
  · apply Real.rpow_pos_of_pos (by linarith)
  · · exact_mod_cast h

/-- Negating both sides: `x·a ≤ b` implies `−b ≤ x·(−a)`. -/
private lemma neg_le_mul_neg_of_mul_le (a b x : ℝ) (h : x * a ≤ b) :
    -b ≤ x * -a := by
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
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [inv_inv]))
      (add norm 0 (by grind only [le_inv']))
      (add norm 0 (by grind only [EReal.neg_le_neg_iff]))
      (add norm 0 (by grind only [EReal.neg_le]))
      (add norm 0 (by grind only [neg_inv]))
      (add norm 0 (by grind only [EReal.le_neg_of_le_neg]))
      (add norm 0 (by grind only [inv_neg]))
      (add norm 0 (by grind only [Pi.inv_apply]))
      (add norm 0 (by grind only [slope_neg]))
      (add norm 0 (by grind only [AkraBazziRecurrence.GrowsPolynomially.iff_eventuallyEq]))
      (add norm 0 (by grind only [Real.sq_le]))
      (add norm 0 (by grind only [MeasureTheory.average_neg]))
      (add norm 0 (by grind only [mabs_of_le_one]))
      (add norm 0 (by grind only [SetTheory.PGame.neg_le_iff]))
      (add unsafe 10% (by grind only [inv_le_inv_iff]))
      (add unsafe 10% (by grind only [inv_le']))
      (add unsafe 10% (by grind only [inv_mabs_le]))
      (add unsafe 50% (by nlinarith [one_le_inv_of_le_one]))
      (add unsafe 50% (by nlinarith [Real.neg_pi_div_two_le_arcsin]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_neg_left]))
      (add unsafe 50% (by nlinarith [Real.log_nonpos]))
      (add unsafe 50% (by nlinarith [mul_inv]))
      (add unsafe 50% (by nlinarith [neg_mul]))
      (add unsafe 50% (by nlinarith [le_inv]))
      (add unsafe 50% (by nlinarith [inv_le]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [Real.arcsin_neg]))
      (add unsafe 50% (by nlinarith [neg_le_of_abs_le]))
      (add unsafe 50% (by nlinarith [neg_eq]))
      (add unsafe 50% (by nlinarith [Real.norm_of_nonpos]))
      (add unsafe 50% (by nlinarith [inv_div]))
      (add unsafe 50% (by nlinarith [neg_div]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [mul_neg, neg_le_neg_iff]

/-- The thesis's step "solving `P_N ≥ q` gives `N ≥ log(1−q)/log(1−p)`": an `N` that reaches the
threshold satisfies `−log(1−q) ≤ N · (−log(1−p))`. -/
private theorem neg_log_le_of_reaches {q p : ℝ} (hp1 : p < 1) {N : ℕ}
    (hN : q ≤ 1 - (1 - p) ^ N) : -Real.log (1 - q) ≤ N * -Real.log (1 - p) :=
  -- `(1−p)^N ≤ 1 − q`; take logs, then negate
  neg_le_mul_neg_of_mul_le _ _ _ (mul_log_le_log_of_pow_le p q N hp1 (le_sub_comm.1 hN))

/-- `log x ≥ 1 − 1/x` with `x = 1 − p > 0`: `1 − (1 − p)⁻¹ ≤ log(1 − p)`. -/
private lemma one_sub_inv_le_log_one_sub (p : ℝ) (hp1 : p < 1) :
    1 - (1 - p)⁻¹ ≤ Real.log (1 - p) := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  exact Real.one_sub_inv_le_log_of_pos (by linarith)

/-- Multiplying both sides by `1 − p > 0`: `1 − (1 − p)⁻¹ ≤ a` implies `(1 − p)·(−a) ≤ p`. -/
private lemma one_sub_mul_neg_le_of_le (p a : ℝ) (hp1 : p < 1) (h : 1 - (1 - p)⁻¹ ≤ a) :
    (1 - p) * -a ≤ p := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  have hp0 : 0 < 1 - p := sub_pos.2 hp1
  rw [mul_comm]
  rw [sub_le_iff_le_add] at h
  field_simp at h
  linarith

/-- The half of the thesis's `log(1−p) = −p + O(p²)` that is used: `−log(1−p) ≤ p/(1−p)`, written as
`(1−p)(−log(1−p)) ≤ p`. -/
private theorem one_sub_mul_neg_log_le {p : ℝ} (hp1 : p < 1) :
    (1 - p) * -Real.log (1 - p) ≤ p :=
  one_sub_mul_neg_le_of_le p _ hp1 (one_sub_inv_le_log_one_sub p hp1)

/-- Multiplying both sides by `1 − p ≥ 0` (`p < 1`): `L ≤ N·a` implies `L(1 − p) ≤ N·a·(1 − p)`. -/
private lemma mul_one_sub_le_mul_one_sub (L N a p : ℝ) (hp1 : p < 1) (he : L ≤ N * a) :
    L * (1 - p) ≤ N * a * (1 - p) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [mul_nonneg_iff_of_pos_right]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [mul_le_iff_le_one_left]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [mul_le_iff_le_one_right]))
      (add unsafe 50% (by nlinarith [mul_nonneg_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul'']))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [mul_nonneg_iff_left_nonneg_of_pos]))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [Real.pi_gt_three]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [sub_pos, mul_le_mul_iff_left₀]

/-- Multiplying both sides by `N ≥ 0`: `(1 − p)·a ≤ p` implies `N·a·(1 − p) ≤ N·p`. -/
private lemma mul_mul_one_sub_le (N a p : ℝ) (hN0 : 0 ≤ N) (hf : (1 - p) * a ≤ p) :
    N * a * (1 - p) ≤ N * p := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
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
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_right']))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right]))
      (add unsafe 50% (by nlinarith [mul_le_one]))
      (add unsafe 50% (by nlinarith [unitInterval.le_one]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left']))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (nlinarith)

/-- Dividing both sides by `p > 0`: `L(1 − p) ≤ N·p` implies `L/p ≤ N + L`. -/
private lemma div_le_add_of_mul_one_sub_le (L N p : ℝ) (hp0 : 0 < p)
    (h : L * (1 - p) ≤ N * p) :
    L / p ≤ N + L := by
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
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
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
      (add norm 0 (by grind only [le_div_iff]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by rw [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Real.sqrt_one_add_le]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Complex.mul_angle_le_norm_sub]))
      (add safe 1 (by unfold div_le_iff))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [div_eq_mul_inv]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [Behrend.two_div_one_sub_two_div_e_le_eight]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 10% (by field_simp [Real.mul_le_sin] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (field_simp [*] at *)
  --   (linarith)

/-- The two one-sided bounds combine into a bound on the absolute value: `N < x + 1`, `x ≤ N + L`,
and `L ≥ 0` imply `|N − x| ≤ L + 1`. -/
private lemma abs_sub_le_of_lt_add_one_of_le_add (N x L : ℝ) (hL : 0 ≤ L) (h1 : N < x + 1)
    (h2 : x ≤ N + L) :
    |N - x| ≤ L + 1 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
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
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [abs_le]))
      (add norm 0 (by grind only [inv_mabs_le]))
      (add norm 0 (by rw [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [inv_le_inv_iff]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [inv_le_mabs]))
      (add norm 0 (by grind only [le_mabs_self]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [Set.mem_Icc_iff_abs_le]))
      (add norm 0 (by grind only [inv_le_div_iff_le_mul]))
      (add norm 0 (by grind only [mabs_div_comm]))
      (add norm 0 (by rw [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [abs_dist_sub_le]))
      (add norm 0 (by grind only [inv_mul']))
      (add norm 0 (by grind only [div_eq_inv_mul]))
      (add norm 0 (by grind only [Real.dist_le_of_mem_Icc]))
      (add norm 0 (by grind only [mabs_le_mabs]))
      (add norm 0 (by grind only [mabs_of_le_one]))
      (add norm 0 (by grind only [mabs_le']))
      (add norm 0 (by grind only [abs_max_sub_max_le_max]))
      (add norm 0 (by grind only [inv_le']))
      (add norm 0 (by grind only [AkraBazziRecurrence.GrowsPolynomially.mul]))
      (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul]))
      (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_one_sub_mul]))
      (add norm 0 (by grind only [div_neg]))
      (add safe 1 (by simp_all only [div_eq_mul_inv]))
      (add safe 1 (by simp_all only [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [neg_div]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (grind only [abs_le])

/-- Explicit version of the thesis's `N = −log(1−q)/p · (1 + O(p))`: for `p ∈ (0,1)`,
`|N − (−log(1−q))/p| ≤ −log(1−q) + 1`. -/
private theorem abs_minSamples_sub_le {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p)
    (hp1 : p < 1) :
    |(minSamples q p : ℝ) - -Real.log (1 - q) / p| ≤ -Real.log (1 - q) + 1 := by
  have hL := neg_log_one_sub_pos q hq0 hq1
  -- Upper bound: `N ≤ ⌈L/p⌉ < L/p + 1`
  have hK := cast_lt_div_add_one_of_le_ceil _ p _ hL.le hp0
    (minSamples_le_ceil hq0 hq1 hp0 hp1.le)
  -- Lower bound: `L ≤ N · (−log(1−p))` and `(1−p)(−log(1−p)) ≤ p` give `L(1−p) ≤ Np`,
  -- so `L/p ≤ N + L`
  have he := neg_log_le_of_reaches hp1 (minSamples_spec hq0 hq1 hp0 hp1.le).1
  have hf := one_sub_mul_neg_log_le hp1
  have hlow := (mul_one_sub_le_mul_one_sub _ _ _ p hp1 he).trans
    (mul_mul_one_sub_le _ _ p (Nat.cast_nonneg _) hf)
  exact abs_sub_le_of_lt_add_one_of_le_add _ _ _ hL.le hK
    (div_le_add_of_mul_one_sub_le _ _ p hp0 hlow)

/-- As `p → 0⁺`, eventually `0 < p < 1`. -/
private lemma eventually_pos_lt_one :
    ∀ᶠ p in 𝓝[>] (0 : ℝ), 0 < p ∧ p < 1 := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  have h1 : ∀ᶠ p in 𝓝[>] (0 : ℝ), 0 < p := self_mem_nhdsWithin
  have h2 : ∀ᶠ p in 𝓝[>] (0 : ℝ), p < 1 := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  exact h1.and h2

/-- For `p > 0`, `1/p ≥ 0`. -/
private lemma one_div_nonneg_of_pos (p : ℝ) (hp0 : 0 < p) :
    0 ≤ 1 / p := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
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
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [Real.rpow_nonneg]))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [one_div_le]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [one_div_nonneg]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_iff))
      (add unsafe 90% (by simp only [one_le_div] at *))
      (add unsafe 10% (by grind only [le_of_lt]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [Real.rpow_pos_of_pos]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 10% (by grind only [Real.rpow_le_rpow]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 10% (by grind only [Real.rpow_one]))
      (add unsafe 10% (by grind only [Real.log_nonneg]))
      (add unsafe 10% (by grind only [Real.rpow_le_rpow_iff]))
      (add unsafe 50% (by nlinarith [Behrend.dValue_pos]))
      (add unsafe 10% (by grind only [eq_or_lt_of_le]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r_lower_bound_on_verticalStrip]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [Real.mul_log_nonneg]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 10% (by grind only [Real.mul_rpow]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [one_div, inv_nonneg]
  --   (linarith)

/-- `x ≤ c/p` rewritten as `x ≤ c·(1/p)`. -/
private lemma le_mul_one_div_of_le_div (x c p : ℝ) (h : x ≤ c / p) :
    x ≤ c * (1 / p) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 100 (by exfalso))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_div_left]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
      (add norm 0 (by grind only [one_div_le]))
      (add norm 0 (by grind only [same_sub_div]))
      (add norm 0 (by grind only [NNReal.le_div_iff]))
      (add norm 0 (by grind only [div_sub']))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [div_le_self]))
      (add norm 0 (by grind only [Behrend.two_div_one_sub_two_div_e_le_eight]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [le_div_comm]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold mul_le_mul_left))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 1 (by unfold div_le_div_right))
      (add safe 1 (by unfold mul_le_mul_right))
      (add safe 1 (by unfold div_le_one))
      (add safe 1 (by unfold one_le_div))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [one_div]
  --   (bound)

/-- Multiplying both sides by `1/q > 0`: `q/p ≤ x` implies `1/p ≤ (1/q)·x`. -/
private lemma one_div_le_of_div_le (q p x : ℝ) (hq0 : 0 < q) (hp0 : 0 < p) (h : q / p ≤ x) :
    1 / p ≤ 1 / q * x := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
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
      (add safe 100 (by ring))
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
      (add norm 0 (by grind only [div_le_div_left]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add norm 0 (by grind only [div_eq_inv_mul]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
      (add norm 0 (by grind only [one_div_le]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [Real.rpow_sub]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold mul_le_mul_left))
      (add safe 1 (by unfold div_le_div_right))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 1 (by unfold div_le_one))
      (add safe 1 (by unfold one_le_div))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [ceilDiv_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [one_div]
  --   (field_simp [*] at *)
  --   simp_all only

/-- The norm of a nonnegative real number is the number itself: for `x, y ≥ 0`, `x ≤ c·y` is exactly
`‖x‖ ≤ c·‖y‖`. -/
private lemma norm_le_mul_norm_of_nonneg (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ c * y) :
    ‖x‖ ≤ c * ‖y‖ := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [Real.norm_of_nonneg, Real.norm_of_nonneg] <;> assumption

/-- Lemma 2.7: `N ∈ Θ(1/p_s)` (as `p_s → 0⁺`). -/
theorem minSamples_isTheta {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (fun p : ℝ => (minSamples q p : ℝ)) =Θ[𝓝[>] 0] (fun p : ℝ => 1 / p) := by
  refine ⟨IsBigO.of_bound (-Real.log (1 - q) + 1) ?_, IsBigO.of_bound (1 / q) ?_⟩
  · -- `N ≤ (L + 1)/p = (L + 1) · (1/p)`
    filter_upwards [eventually_pos_lt_one] with p hp
    exact norm_le_mul_norm_of_nonneg _ _ _ (Nat.cast_nonneg _) (one_div_nonneg_of_pos p hp.1)
      (le_mul_one_div_of_le_div _ _ p (minSamples_le_div hq0 hq1 hp.1 hp.2.le))
  · -- `q/p ≤ N` gives `1/p ≤ (1/q) · N`
    filter_upwards [eventually_pos_lt_one] with p hp
    exact norm_le_mul_norm_of_nonneg _ _ _ (one_div_nonneg_of_pos p hp.1) (Nat.cast_nonneg _)
      (one_div_le_of_div_le q p _ hq0 hp.1 (div_le_minSamples hq0 hq1 hp.1 hp.2.le))

/-- The more precise conclusion `N = −log(1−q)/p · (1 + O(p))` in the proof of Lemma 2.7, which is
equivalent to `N − (−log(1−q))/p = O(1)` (as `p → 0⁺`). -/
theorem minSamples_sub_isBigO {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (fun p : ℝ => (minSamples q p : ℝ) - -Real.log (1 - q) / p) =O[𝓝[>] 0]
      (fun _ : ℝ => (1 : ℝ)) := by
  -- `O(1)` means eventually bounded: `|N − L/p| ≤ L + 1`
  refine (isBigO_one_iff ℝ).2 (isBoundedUnder_of_eventually_le (a := -Real.log (1 - q) + 1) ?_)
  filter_upwards [eventually_pos_lt_one] with p hp
  exact abs_minSamples_sub_le hq0 hq1 hp.1 hp.2

/-- Explicit constants: for all `p ∈ (0, 1]`, `q/p ≤ N ≤ (−log(1−q) + 1)/p`. The lower bound is the
union bound: `q ≤ 1 − (1−p)^N ≤ N·p` (Bernoulli's inequality); the upper bound takes
`K = ⌈−log(1−q)/p⌉`, since `(1−p)^K ≤ e^{−pK} ≤ 1 − q`. Corollary 2.8 uses these constants. -/
theorem minSamples_bounds {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    q / p ≤ minSamples q p ∧ (minSamples q p : ℝ) ≤ (-Real.log (1 - q) + 1) / p := by
  exact ⟨div_le_minSamples hq0 hq1 hp0 hp1, minSamples_le_div hq0 hq1 hp0 hp1⟩

/-- The first step of the proof of Corollary 2.8, "the contexts are searched independently, so
`N_𝒞 = Σ_C N_C`": each context `C` is allotted `n_C` samples; for every context to reach, on its
own, "probability of at least one success ≥ `q`", the smallest total number of verifications is
exactly `Σ_C N_C` (`N_C = minSamples q (p C)`; one sample counts as one verification). -/
theorem perContext_minTotal {ι : Type*} (s : Finset ι) (p : ι → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hp : ∀ C ∈ s, 0 < p C ∧ p C ≤ 1) :
    IsLeast {T : ℕ | ∃ n : ι → ℕ, (∀ C ∈ s, q ≤ 1 - (1 - p C) ^ n C) ∧ T = ∑ C ∈ s, n C}
      (∑ C ∈ s, minSamples q (p C)) := by
  -- Membership: take `n C = N_C`; lower bound: each term has `N_C ≤ n C` (`minSamples_spec`)
  refine ⟨⟨fun C => minSamples q (p C),
    fun C hC => (minSamples_spec hq0 hq1 (hp C hC).1 (hp C hC).2).1, rfl⟩, ?_⟩
  rintro T ⟨n, hn, rfl⟩
  exact Finset.sum_le_sum fun C hC =>
    (minSamples_spec hq0 hq1 (hp C hC).1 (hp C hC).2).2 _ (hn C hC)

/-- `q/p ≤ x` rewritten as `q·(1/p) ≤ x`. -/
private lemma mul_one_div_le_of_div_le (q p x : ℝ) (h : q / p ≤ x) :
    q * (1 / p) ≤ x := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
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
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_div_left]))
      (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [one_div_le]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_self]))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add norm 0 (by grind only [same_sub_div]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [le_div_comm]))
      (add norm 0 (by grind only [Complex.mul_angle_le_norm_sub]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [div_sub']))
      (add norm 0 (by grind only [ContractingWith.dist_le_of_fixedPoint]))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold div_le_div_right))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 1 (by unfold div_le_one))
      (add safe 1 (by unfold one_le_div))
      (add safe 0 (by nlinarith [Real.mul_le_sin]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [Behrend.two_div_one_sub_two_div_e_le_eight]))
      (add unsafe 50% (by nlinarith [ceilDiv_le_iff_le_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [one_div]
  --   (ring)
  --   (bound)

/-- Corollary 2.8: finitely many contexts (`s`), each with proving probability `p_C ∈ (0, 1]`.
"Probability at least `q`" is a requirement on each context separately (the reading used in the
thesis's proof), so `N_𝒞 = Σ_C N_C` with `N_C = minSamples q (p C)` (see `perContext_minTotal`). The
constants depend only on `q`, not on the number of contexts or on the individual `p_C`:
`q · Σ_C 1/p_C ≤ N_𝒞 ≤ (−log(1−q) + 1) · Σ_C 1/p_C`, that is, `N_𝒞 ∈ Θ(Σ_C 1/p_C)`. -/
theorem perContext_bounds {ι : Type*} (s : Finset ι) (p : ι → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hp : ∀ C ∈ s, 0 < p C ∧ p C ≤ 1) :
    q * ∑ C ∈ s, 1 / p C ≤ ∑ C ∈ s, (minSamples q (p C) : ℝ) ∧
      ∑ C ∈ s, (minSamples q (p C) : ℝ) ≤ (-Real.log (1 - q) + 1) * ∑ C ∈ s, 1 / p C := by
  -- Move the constant inside the sum (`Finset.mul_sum`), apply `minSamples_bounds` to each `C`,
  -- then sum termwise
  constructor
  · calc q * ∑ C ∈ s, 1 / p C = ∑ C ∈ s, q * (1 / p C) := Finset.mul_sum _ _ _
      _ ≤ ∑ C ∈ s, (minSamples q (p C) : ℝ) := Finset.sum_le_sum fun C hC =>
          mul_one_div_le_of_div_le q (p C) _ (minSamples_bounds hq0 hq1 (hp C hC).1 (hp C hC).2).1
  · calc ∑ C ∈ s, (minSamples q (p C) : ℝ) ≤ ∑ C ∈ s, (-Real.log (1 - q) + 1) * (1 / p C) :=
          Finset.sum_le_sum fun C hC =>
            le_mul_one_div_of_le_div _ _ (p C) (minSamples_bounds hq0 hq1 (hp C hC).1 (hp C hC).2).2
      _ = (-Real.log (1 - q) + 1) * ∑ C ∈ s, 1 / p C := (Finset.mul_sum _ _ _).symm

/-- Last sentence of Remark 2.6: at a uniform initialization, `π(·∣C)` is uniform over `𝒜`
(`policy_zero`), and uniform random search is exactly sampling from the initial policy, with proving
probability `p_0 = |𝒜*|/M^H` (`provingProb_zero`). By Lemma 2.7, it needs `Θ(1/p_0)` samples, with
constants independent of `H`, `M`, and `𝒜*`. -/
theorem uniformSearch_bounds {H M : ℕ} (hM : 0 < M) (Astar : Finset (Arm H M))
    (hA : Astar.Nonempty) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q / provingProb Astar 0 ≤ minSamples q (provingProb Astar 0) ∧
      (minSamples q (provingProb Astar 0) : ℝ) ≤ (-Real.log (1 - q) + 1) / provingProb Astar 0 := by
  -- `minSamples_bounds` with `p := p_s(0) ∈ (0, 1]`
  exact minSamples_bounds hq0 hq1 (provingProb_pos Astar hA 0) (provingProb_le_one hM Astar 0)

end Sec2

end

-- ===== project/Sec2/DSP/Basic.lean =====
section

set_option maxHeartbeats 0

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
  have hS1 : expectedReward Astar rs rf l = (rs - rf) * provingProb Astar l + rf := by
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hM hsum
    unfold expectedReward provingProb
    rw [← Finset.sum_add_sum_compl Astar] at hsum ⊢
    have e1 : ∑ A ∈ Astar, policy l A * reward Astar rs rf A = ∑ A ∈ Astar, policy l A * rs :=
      Finset.sum_congr rfl fun A hA => by simp [reward, hA]
    have e2 : ∑ A ∈ Astarᶜ, policy l A * reward Astar rs rf A = ∑ A ∈ Astarᶜ, policy l A * rf :=
      Finset.sum_congr rfl fun A hA => by simp [reward, Finset.mem_compl.mp hA]
    rw [e1, e2, ← Finset.sum_mul, ← Finset.sum_mul]
    linear_combination rf * hsum
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
  have hS2 : gradient (expectedReward Astar rs rf) l = (rs - rf) • gradient (provingProb Astar) l := by
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - hS1 hdiff
    ext
    simp [hS1, gradient, hdiff, fderiv_const_mul]
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
  have hS3 : ‖gradient (fun θ' => expectedReward Astar rs rf (net θ')) θ‖ ≤ ‖fderiv ℝ net θ‖ * ‖gradient (expectedReward Astar rs rf) (net θ)‖ := by
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hnet hJdiff
    have hc : HasFDerivAt (fun θ' => expectedReward Astar rs rf (net θ'))
        ((fderiv ℝ (expectedReward Astar rs rf) (net θ)).comp (fderiv ℝ net θ)) θ :=
      hJdiff.hasFDerivAt.comp θ hnet.hasFDerivAt
    have e1 : ‖gradient (fun θ' => expectedReward Astar rs rf (net θ')) θ‖ =
        ‖fderiv ℝ (fun θ' => expectedReward Astar rs rf (net θ')) θ‖ := by
      rw [gradient]
      exact LinearIsometryEquiv.norm_map _ _
    have e2 : ‖gradient (expectedReward Astar rs rf) (net θ)‖ =
        ‖fderiv ℝ (expectedReward Astar rs rf) (net θ)‖ := by
      rw [gradient]
      exact LinearIsometryEquiv.norm_map _ _
    rw [e1, e2, hc.fderiv, mul_comm]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  exact hS3

end Sec2.DSP

end

-- ===== project/Sec2/DSP/SelfBound.lean =====
section

set_option maxHeartbeats 0

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
      -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
      -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
      -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
      -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
      clear * -
      intro l₁ h' hh' v t
      have key : ∀ m' : Fin M,
          (l₁ + t • EuclideanSpace.single (h, m) (1 : ℝ)) (h', m') = l₁ (h', m') := by
        intro m'
        have hne : (h', m') ≠ (h, m) := fun he => hh' (congrArg Prod.fst he)
        simp [hne]
      simp only [softmax, key]
    have hL5 : ∀ A : Arm H M,
        (∏ h' ∈ Finset.univ.erase h, softmax l h' (A h')) * softmax l h (A h) = policy l A := by
      -- [L23.5] ∏_{h'≠h} π^(h')(v_{h'}|C) · π^(h)(v_h|C) = π(A|C)   (the underbrace of l.86)
      -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
      -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
      -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
      -- (indentation adjusted only).
      clear * -
      intro A
      simp_rw [policy, mul_comm]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ h)]
      rw [mul_comm]
    -- [aux, cite: softmax_pos] π^(h)(m'|C) > 0 for every level m' (used by L23.8)
    have hsm : ∀ m' : Fin M, 0 < softmax l h m' := fun m' => softmax_pos l h m'
    -- [aux, cite: sum_softmax] Σ_{m'} π^(h)(m'|C) = 1 when 0 < M (used by L23.8)
    have hsum : 0 < M → ∑ m' : Fin M, softmax l h m' = 1 := fun hM => sum_softmax hM l h
    have hL8 : ∀ A : Arm H M, |(if A h = m then (1 : ℝ) else 0) - softmax l h m| ≤ 1 := by
      -- [L23.8] |1(·) − π^(h)(m|C)| ≤ 1, with 1(·) = 1(v_h = m)
      -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
      -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
      -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
      -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
      clear * - hsm hsum
      intro A
      have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) m.isLt
      have hpos : 0 < softmax l h m := hsm m
      have hle : softmax l h m ≤ 1 := le_trans (Finset.single_le_sum (fun i _ => (hsm i).le) (Finset.mem_univ m)) (hsum hM).le
      rw [abs_le]
      split_ifs <;> constructor <;> linarith
    calc |fderiv ℝ (provingProb Astar) l (EuclideanSpace.single (h, m) (1 : ℝ))|
        _ = |∑ A ∈ Astar, fderiv ℝ (fun l' : Logits H M => ∏ h' : Fin H, softmax l' h' (A h')) l
              (EuclideanSpace.single (h, m) (1 : ℝ))| := by
          -- [L23.2] |∂_{l_h^m} p_s| = |Σ_{A∈𝒜*} ∂_{l_h^m} ∏_{h'} π^(h')(v_{h'}|C)|
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 3 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * - hdiffπ
          have hd : ∀ A ∈ Astar,
              DifferentiableAt ℝ (fun l' : Logits H M => ∏ h', softmax l' h' (A h')) l := by
            intro A _
            have e : (provingProb {A} : Logits H M → ℝ) = fun l' => ∏ h', softmax l' h' (A h') := by
              funext l'
              simp only [provingProb, policy, Finset.sum_singleton]
            have hA := hdiffπ A l
            rw [e] at hA
            exact hA
          have key : fderiv ℝ (provingProb Astar) l =
              ∑ A ∈ Astar, fderiv ℝ (fun l' : Logits H M => ∏ h', softmax l' h' (A h')) l := by
            have e : (provingProb Astar : Logits H M → ℝ) =
                fun l' => ∑ A ∈ Astar, ∏ h', softmax l' h' (A h') := by
              funext l'
              rfl
            rw [e]
            exact fderiv_fun_sum hd
          rw [key]
          rw [ContinuousLinearMap.sum_apply]
        _ = |∑ A ∈ Astar, (∏ h' ∈ Finset.univ.erase h, softmax l h' (A h')) *
              fderiv ℝ (fun l' : Logits H M => softmax l' h (A h)) l
                (EuclideanSpace.single (h, m) (1 : ℝ))| := by
          -- [L23.3] = |Σ_{A∈𝒜*} (∏_{h'≠h} π^(h')(v_{h'}|C)) · ∂_{l_h^m} π^(h)(v_h|C)|   (only π^(h) depends on l_h^m)
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * - hL1
          have hc : ∀ i : Fin H × Fin M, DifferentiableAt ℝ (fun l' : Logits H M => l' i) l := by
            intro i
            exact (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt
          have hS : ∀ (h' : Fin H) (v : Fin M), DifferentiableAt ℝ (fun l' : Logits H M => softmax l' h' v) l := by
            intro h' v
            have hpos : 0 < ∑ m' : Fin M, Real.exp (l (h', m')) :=
              Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨m, Finset.mem_univ _⟩
            have hnum : DifferentiableAt ℝ (fun l' : Logits H M => Real.exp (l' (h', v))) l := (hc (h', v)).exp
            have hden : DifferentiableAt ℝ (fun l' : Logits H M => ∑ m' : Fin M, Real.exp (l' (h', m'))) l := by
              exact DifferentiableAt.fun_sum fun i _ => (hc (h', i)).exp
            show DifferentiableAt ℝ (fun l' : Logits H M => Real.exp (l' (h', v)) / ∑ m' : Fin M, Real.exp (l' (h', m'))) l
            first
              | exact hnum.div hden hpos.ne'
              | exact hnum.mul (hden.inv hpos.ne')
          have hP : ∀ A : Arm H M, DifferentiableAt ℝ (fun l' : Logits H M => ∏ h' : Fin H, softmax l' h' (A h')) l := by
            intro A
            rw [show (fun l' : Logits H M => ∏ h' : Fin H, softmax l' h' (A h')) = Sec2.provingProb {A} from funext fun l' => (by simp [Sec2.provingProb, Sec2.policy])]
            exact Sec2.differentiable_provingProb {A} l
          have key : ∀ f : Logits H M → ℝ, DifferentiableAt ℝ f l →
              fderiv ℝ f l (EuclideanSpace.single (h, m) (1:ℝ)) =
                deriv (fun t : ℝ => f (l + t • EuclideanSpace.single (h, m) (1:ℝ))) 0 := by
            intro f hf
            exact hf.lineDeriv_eq_fderiv.symm
          have hA : ∀ A : Arm H M,
              fderiv ℝ (fun l' : Logits H M => ∏ h' : Fin H, softmax l' h' (A h')) l (EuclideanSpace.single (h, m) (1:ℝ)) =
                (∏ h' ∈ Finset.univ.erase h, softmax l h' (A h')) *
                  fderiv ℝ (fun l' : Logits H M => softmax l' h (A h)) l (EuclideanSpace.single (h, m) (1:ℝ)) := by
            intro A
            have hfun : (fun t : ℝ => ∏ h' : Fin H, softmax (l + t • EuclideanSpace.single (h, m) (1:ℝ)) h' (A h')) =
                fun t : ℝ => (∏ h' ∈ Finset.univ.erase h, softmax l h' (A h')) *
                  softmax (l + t • EuclideanSpace.single (h, m) (1:ℝ)) h (A h) := by
              funext t
              rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ h)]
              exact congrArg (· * softmax (l + t • EuclideanSpace.single (h, m) (1:ℝ)) h (A h)) (Finset.prod_congr rfl fun h' hh' => hL1 l h' (Finset.ne_of_mem_erase hh') (A h') t)
            exact (key _ (hP A)).trans ((congrArg (fun g : ℝ → ℝ => deriv g 0) hfun).trans ((deriv_const_mul_field _).trans (congrArg (fun x : ℝ => (∏ h' ∈ Finset.univ.erase h, softmax l h' (A h')) * x) (key _ (hS h (A h))).symm)))
          exact congrArg (fun x : ℝ => |x|) (Finset.sum_congr rfl fun A _ => hA A)
        _ = |∑ A ∈ Astar, ((∏ h' ∈ Finset.univ.erase h, softmax l h' (A h')) * softmax l h (A h)) *
              ((if A h = m then (1 : ℝ) else 0) - softmax l h m)| := by
          -- [L23.4] = |Σ_{A∈𝒜*} (∏_{h'≠h} π^(h')(v_{h'}|C) · π^(h)(v_h|C)) · (1(v_h = m) − π^(h)(m|C))|   (the softmax derivative)
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * -
          have hproj : ∀ i : Fin H × Fin M,
              HasFDerivAt (fun l' : Logits H M => l' i) (EuclideanSpace.proj i : Logits H M →L[ℝ] ℝ) l := by
            intro i
            exact (EuclideanSpace.proj i : Logits H M →L[ℝ] ℝ).hasFDerivAt
          have hSum : HasFDerivAt (fun l' : Logits H M => ∑ m' : Fin M, Real.exp (l' (h, m')))
              (∑ m' : Fin M, Real.exp (l (h, m')) • (EuclideanSpace.proj (h, m') : Logits H M →L[ℝ] ℝ)) l := by
            first
              | exact HasFDerivAt.sum (fun m' _ => (hproj (h, m')).exp)
              | exact HasFDerivAt.fun_sum (fun m' _ => (hproj (h, m')).exp)
          have hv2 : (∑ m' : Fin M, Real.exp (l (h, m')) • (EuclideanSpace.proj (h, m') : Logits H M →L[ℝ] ℝ))
              (EuclideanSpace.single (h, m) 1) = Real.exp (l (h, m)) := by
            simp [EuclideanSpace.single_apply, mul_ite, Finset.sum_ite_eq']
          have key : ∀ a : Fin M,
              (fderiv ℝ (fun l' : Logits H M => softmax l' h a) l) (EuclideanSpace.single (h, m) 1) =
                softmax l h a * ((if a = m then 1 else 0) - softmax l h m) := by
            intro a
            have hS : (0 : ℝ) < ∑ m' : Fin M, Real.exp (l (h, m')) :=
              Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨a, Finset.mem_univ a⟩
            have hv1 : (EuclideanSpace.proj (h, a) : Logits H M →L[ℝ] ℝ) (EuclideanSpace.single (h, m) 1) =
                if a = m then 1 else 0 := by
              by_cases ham : a = m
              · subst ham; simp [EuclideanSpace.single_apply]
              · simp [EuclideanSpace.single_apply, ham]
            have hinv : HasFDerivAt (fun y : Logits H M => (∑ m' : Fin M, Real.exp (y (h, m')))⁻¹)
                ((-((∑ m' : Fin M, Real.exp (l (h, m'))) ^ 2)⁻¹) •
                  (∑ m' : Fin M, Real.exp (l (h, m')) • (EuclideanSpace.proj (h, m') : Logits H M →L[ℝ] ℝ))) l :=
              (hasDerivAt_inv hS.ne').comp_hasFDerivAt l hSum
            simp only [softmax, div_eq_mul_inv]
            rw [((hproj (h, a)).exp.fun_mul hinv).fderiv]
            simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
              hv1, hv2]
            ring
          congr 1
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [key (A h)]
          ring
        _ = |∑ A ∈ Astar, policy l A * ((if A h = m then (1 : ℝ) else 0) - softmax l h m)| := by
          -- [L23.6] = |Σ_{A∈𝒜*} π(A|C) · (1(v_h = m) − π^(h)(m|C))|   (the underbrace)
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * - hL5
          aesop (config := {
              maxRuleApplications := 1600
              maxNormIterations := 520
              enableUnfold := false
            })
              (add norm 100 (by norm_cast))
              (add norm 0 (by linarith))
              (add norm 0 (by nlinarith))
              (add norm 0 (by positivity))
              (add norm 1 (by push_neg))
              (add norm 0 (by bound))
              (add norm 0 (by ring_nf))
              (add norm 1 (by ext))
              (add norm 100 (by exfalso))
              (add norm 1 (by simp))
              (add norm 1 (by field_simp [*] at *))
              (add safe 100 (by ring))
              (add safe 100 (by field_simp))
              (add safe 100 (by norm_num))
              (add safe 100 (by omega))
              (add safe 100 (by interval_cases))
              (add safe 0 (by split))
              (add safe 100 (by decide))
              (add safe 0 (by push_cast))
              (add safe 100 (by assumption_mod_cast))
              (add norm 0 (by grind only [Finset.mul_sum]))
              (add norm 0 (by grind only [Finset.sum_mul]))
              (add norm 0 (by grind only [Finset.prod_congr]))
              (add norm 0 (by grind only [Nat.cast_sum]))
              (add norm 0 (by grind only [Finset.prod_sigma']))
              (add norm 0 (by grind only [norm_sum_le]))
              (add norm 0 (by grind only [VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le]))
              (add unsafe 90% (by rw [Finset.prod_mul_distrib]))
              (add unsafe 90% (by rw [Finset.univ]))
              (add unsafe 90% (by rw [Fintype.prod_congr]))
              (add unsafe 90% (by rw [Finset.prod_const]))
              (add unsafe 90% (by rw [Finset.prod]))
              (add unsafe 90% (by rw [Finset.prod_comm]))
              (add unsafe 90% (by rw [NumberField.InfinitePlace.prod_eq_abs_norm]))
              (add unsafe 90% (by rw [Finset.abs_prod]))
              (add unsafe 90% (by rw [Finset.abs_sum_of_nonneg']))
              (add unsafe 90% (by rw [Finset.prod_le_prod']))
              (add unsafe 90% (by rw [Finset.abs_sum_of_nonneg]))
              (add unsafe 90% (by rw [Finset.prod_subset]))
              (add unsafe 90% (by rw [Finset.prod_div_distrib]))
              (add unsafe 90% (by rw [Finset.card_fin]))
              (add unsafe 90% (by rw [Finset.prod_erase_mul]))
              (add unsafe 90% (by rw [Finset.prod_apply]))
              (add unsafe 90% (by rw [Finset.prod_attach]))
              (add unsafe 90% (by rw [Real.rpow_sum_le_const_mul_sum_rpow]))
              (add unsafe 90% (by rw [Finset.prod_eq_zero]))
              (add unsafe 90% (by rw [NumberField.mixedEmbedding.convexBodySumFun_apply]))
              (add unsafe 90% (by rw [abs_pow]))
              (add unsafe 90% (by rw [Finset.prod_subtype]))
              (add unsafe 90% (by rw [abs_mul]))
              (add unsafe 90% (by rw [Finset.prod_le_univ_prod_of_one_le']))
              (add unsafe 90% (by rw [Finset.prod_pow]))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   simp_all only
        _ ≤ ∑ A ∈ Astar, policy l A := by
          -- [L23.7] ≤ Σ_{A∈𝒜*} π(A|C)   (the triangle inequality and L23.8)
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * - hL8 hπ
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun A _ => ?_)
          rw [abs_mul, abs_of_pos (hπ A)]
          exact mul_le_of_le_one_right (hπ A).le (hL8 A)
        _ = provingProb Astar l := by
          -- [L23.9] Σ_{A∈𝒜*} π(A|C) = p_s
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * -
          aesop (config := {
              maxRuleApplications := 1600
              maxRuleApplicationDepth := 380
              maxNormIterations := 320
              enableUnfold := false
            })
              (add norm 100 (by norm_cast))
              (add norm 0 (by linarith))
              (add norm 0 (by nlinarith))
              (add norm 0 (by omega))
              (add norm 1 (by push_neg))
              (add norm 0 (by bound))
              (add norm 100 (by simp_all))
              (add norm 1 (by field_simp [*] at *))
              (add safe 100 (by ring))
              (add safe 100 (by field_simp))
              (add safe 100 (by norm_num))
              (add safe 0 (by positivity))
              (add safe 100 (by interval_cases))
              (add safe 100 (by ring_nf))
              (add safe 0 (by ext))
              (add safe 0 (by split))
              (add safe 0 (by norm_num [*] at *))
              (add safe 100 (by rfl))
              (add safe 100 (by decide))
              (add safe 0 (by push_cast))
              (add safe 100 (by assumption_mod_cast))
              (add norm 0 (by grind only [List.alternatingProd_eq_finset_prod]))
              (add norm 0 (by grind only [QPF.suppPreservation_iff_liftpPreservation]))
              (add norm 0 (by grind only [List.alternatingProd_cons_cons]))
              (add norm 0 (by grind only [ArithmeticFunction.ppow]))
              (add norm 0 (by grind only [SetTheory.PGame.Fuzzy]))
              (add norm 0 (by grind only [List.alternatingProd_cons]))
              (add norm 0 (by grind only [SetTheory.Game.PGame.lf_iff_game_lf]))
              (add norm 0 (by grind only [MvQPF.suppPreservation_iff_liftpPreservation]))
              (add norm 0 (by grind only [List.alternatingProd]))
              (add norm 0 (by grind only [QPF.suppPreservation_iff_uniform]))
              (add norm 0 (by grind only [List.alternatingProd_cons']))
              (add norm 0 (by grind only [List.alternatingProd_cons_cons']))
              (add norm 0 (by grind only [MvQPF.liftpPreservation_iff_uniform]))
              (add norm 0 (by grind only [FirstOrder.Language.BoundedFormula.IsPrenex]))
              (add norm 0 (by grind only [List.alternatingProd_singleton]))
              (add norm 0 (by grind only [Pell.isPell_mul]))
              (add norm 0 (by grind only [SetTheory.PGame.LF]))
              (add norm 0 (by grind only [MvQPF.suppPreservation_iff_isUniform]))
              (add norm 0 (by grind only [SetTheory.Game.PGame.fuzzy_iff_game_fuzzy]))
              (add norm 0 (by grind only [List.alternatingProd_nil]))
              (add norm 0 (by grind only [PFunctor.M.IsPath]))
              (add norm 0 (by grind only [Surreal.Multiplication.IH1]))
              (add norm 0 (by grind only [AlgebraicGeometry.AffineTargetMorphismProperty.toProperty_apply]))
              (add norm 0 (by grind only [PFunctor.M.isPath_cons']))
              (add norm 0 (by grind only [SetTheory.PGame.Equiv]))
              (add norm 0 (by grind only [List.alternatingProd_append]))
              (add norm 0 (by grind only [AlgebraicGeometry.QuasiCompact.affineProperty_toProperty]))
              (add norm 0 (by grind only [MeasureTheory.ProgMeasurable.stoppedProcess]))
              (add norm 0 (by grind only [List.alternatingProd_reverse]))
              (add norm 0 (by grind only [Nat.perfect_iff_sum_divisors_eq_two_mul]))
              (add norm 0 (by grind only [Surreal.Multiplication.P2_neg_right]))
              (add norm 0 (by grind only [TopCat.Sheaf.presheaf]))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   (bound)
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
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 4 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * -
    intro h m
    have key : (InnerProductSpace.toDual ℝ (Logits H M) (gradient (provingProb Astar) l))
        (EuclideanSpace.single (h, m) (1 : ℝ)) =
        (fderiv ℝ (provingProb Astar) l) (EuclideanSpace.single (h, m) (1 : ℝ)) := by
      simp [gradient]
    rw [← key, InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_right]
    simp
  -- l.90–97: summing the HM squared partial derivatives
  calc ‖gradient (expectedReward Astar rs rf) l‖
      _ = (rs - rf) * ‖gradient (provingProb Astar) l‖ := by
        -- [L23.10] ‖∇_l J_sparse‖₂ = Δ_r ‖∇_l p_s‖₂   (the Setup's ∇_l J_sparse = Δ_r ∇_l p_s, and Δ_r > 0)
        -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
        -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
        -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
        -- (indentation adjusted only).
        clear * - hr hgradJ
        by_cases hm : 0 < M
        · rw [hgradJ hm]
          rw [norm_smul] <;> simp [hm, hr.le]
        · simp [gradient, hm]
          have : M = 0 := by omega
          subst this
          simp
      _ = (rs - rf) * Real.sqrt (∑ h : Fin H, ∑ m : Fin M,
            (fderiv ℝ (provingProb Astar) l (EuclideanSpace.single (h, m) (1 : ℝ))) ^ 2) := by
        -- [L23.11] = Δ_r √(Σ_{h,m} (∂_{l_h^m} p_s)²)   (summing the HM squared partial derivatives)
        -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
        -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
        -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
        -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
        clear * - hentry
        rw [EuclideanSpace.norm_eq, Fintype.sum_prod_type]
        simp only [Real.norm_eq_abs, sq_abs, hentry]
      _ ≤ (rs - rf) * Real.sqrt (∑ h : Fin H, ∑ m : Fin M, provingProb Astar l ^ 2) := by
        -- [L23.12] ≤ Δ_r √(Σ_{h,m} p_s²)   (|∂_{l_h^m} p_s| ≤ p_s for every h and m)
        -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
        -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
        -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
        -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
        clear * - hr hpartial
        have hrs : 0 ≤ rs - rf := by linarith
        refine mul_le_mul_of_nonneg_left ?_ hrs
        refine Real.sqrt_le_sqrt ?_
        refine Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun m _ => ?_
        have h1 := abs_le.mp (hpartial h m)
        exact sq_le_sq' h1.1 h1.2
      _ = Real.sqrt ((H : ℝ) * M) * (rs - rf) * provingProb Astar l := by
        -- [L23.13] = √(HM) Δ_r p_s
        -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
        -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
        clear * - hps
        aesop (config := {
            maxRuleApplications := 1600
            maxNormIterations := 320
            maxGoals := 16
            enableUnfold := false
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
            (add safe 100 (by positivity))
            (add safe 100 (by omega))
            (add safe 100 (by interval_cases))
            (add safe 0 (by split))
            (add safe 100 (by norm_cast at *))
            (add safe 100 (by decide))
            (add safe 0 (by push_cast))
            (add safe 100 (by assumption_mod_cast))
            (add norm 0 (by grind only [Finset.mul_sum]))
            (add norm 0 (by grind only [Finset.sum_mul]))
            (add norm 0 (by grind only [Finset.prod_mul_distrib]))
            (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
            (add norm 0 (by grind only [CharTwo.sum_sq]))
            (add norm 0 (by grind only [sq_sum_le_card_mul_sum_sq]))
            (add norm 0 (by grind only [SzemerediRegularity.mul_sq_le_sum_sq]))
            (add norm 0 (by grind only [mul_pow]))
            (add norm 0 (by grind only [PiLp.norm_sq_eq_of_L2]))
            (add norm 0 (by grind only [ProbabilityTheory.sum_variance_truncation_le]))
            (add norm 0 (by grind only [PiLp.inner_apply]))
            (add norm 0 (by grind only [Real.sum_mul_le_sqrt_mul_sqrt]))
            (add norm 0 (by grind only [norm_sub_sq]))
            (add norm 0 (by grind only [pow_two_pow_sub_pow_two_pow]))
            (add norm 0 (by grind only [sq_abs]))
            (add norm 0 (by grind only [PiLp.norm_eq_of_L2]))
            (add norm 0 (by grind only [VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le]))
            (add norm 0 (by grind only [Finset.prod]))
            (add norm 0 (by grind only [Finset.prod_div_distrib]))
            (add norm 0 (by grind only [Real.sqrt_mul]))
            (add norm 0 (by grind only [norm_sub_sq_real]))
            (add norm 0 (by grind only [norm_add_sq]))
            (add norm 0 (by grind only [aux_add]))
            (add norm 0 (by grind only [Real.pow_mul_norm_iteratedFDeriv_fourierIntegral_le]))
            (add norm 0 (by grind only [GaussianFourier.integral_cexp_neg_sum_mul_add]))
            (add norm 0 (by grind only [mul_comm]))
            (add norm 0 (by grind only [GaussianFourier.integrable_cexp_neg_mul_sum_add]))
            (add norm 0 (by grind only [Real.sq_sqrt]))
            (add norm 0 (by grind only [norm_add_sq_real]))
            (add norm 0 (by grind only [GaussianFourier.integrable_cexp_neg_sum_mul_add]))
            (add norm 0 (by grind only [sq_nonneg]))
            (add unsafe 50% (by simp only [sq_sub_sq]))
        -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
        --   simp_all only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_nonneg, Real.sqrt_mul, Real.sqrt_sq]
        --   (linarith)

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
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop finds a proof, but its "Try this" output does not replay (`No goals to be solved`). The proof below
    -- was written by Opus 5.5 (a fresh Claude Code subagent that saw only this gap's goal, its thesis step, the
    -- statements of `Sec2`, and Lean's messages).
    clear * - hS3 hL23
    exact hS3.trans (mul_le_mul_of_nonneg_left hL23 (norm_nonneg _))
  exact hPS1

end Sec2.DSP

end

-- ===== project/Sec2/DSP/Growth.lean =====
section

set_option maxHeartbeats 0

open Finset

namespace Sec2.DSP

variable {H M : ℕ}

/-- Lemma 2.4: for all `0 < α ≤ α₀ = 1 / ((4H + 1) Δ_r)` and all `l`,
`l' = l + α ∇_l J_sparse(l)` satisfies `0 ≤ p_s(l') − p_s(l) ≤ c · p_s(l)²` with
`c = 2 α H M Δ_r`. -/
theorem growth (hM : 0 < M) (Astar : Finset (Arm H M)) (rs rf : ℝ) (hr : rf < rs) :
    ∀ α : ℝ, 0 < α → α ≤ 1 / ((4 * H + 1) * (rs - rf)) → ∀ l : Logits H M,
      0 ≤ provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ∧
      provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ≤
        2 * α * ((H : ℝ) * M) * (rs - rf) * provingProb Astar l ^ 2 := by
  intro α hα hαle l
  -- [cite: gradient_expectedReward] the Setup's ∇_l J_sparse = Δ_r ∇_l p_s at l_k; it turns α ∇_l J_sparse(l_k) into δ
  have hS2 := gradient_expectedReward hM Astar rs rf l
  -- l.112 (definitions, not steps): write ∇_l p_k for ∇_l p_s(l_k), and δ = α Δ_r ∇_l p_k
  set g := gradient (provingProb Astar) l with hg
  set δ := (α * (rs - rf)) • g with hδ
  -- the chain (2.3)
  have h23 : provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l =
      provingProb Astar (l + δ) - provingProb Astar l :=
    calc provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l
        = provingProb Astar (l + α • gradient (expectedReward Astar rs rf) l) -
            provingProb Astar l := by
          -- [L24.1] p_{k+1} − p_k = p_s(l_k + α ∇_l J_sparse(l_k)) − p_s(l_k)
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * -
          aesop (config := {
              maxRuleApplications := 1600
              maxNormIterations := 320
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
              (add norm 1 (by ext))
              (add norm 1 (by simp))
              (add norm 1 (by field_simp [*] at *))
              (add safe 100 (by ring))
              (add safe 100 (by field_simp))
              (add safe 100 (by norm_num))
              (add safe 0 (by positivity))
              (add safe 100 (by interval_cases))
              (add safe 0 (by split))
              (add safe 0 (by norm_num [*] at *))
              (add safe 100 (by rfl))
              (add safe 100 (by decide))
              (add safe 0 (by push_cast))
              (add safe 100 (by assumption_mod_cast))
              (add norm 0 (by grind only [WeakFEPair.Λ₀_eq]))
              (add norm 0 (by grind only [mul_div_cancel_right]))
              (add norm 0 (by grind only [mul_div_cancel_left]))
              (add norm 0 (by grind only [skewAdjointPart]))
              (add norm 0 (by grind only [mul_div_cancel]))
              (add norm 0 (by grind only [aux_sub]))
              (add norm 0 (by grind only [QuadraticForm.map_add_self]))
              (add norm 0 (by grind only [mul_div_mul_comm]))
              (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux7]))
              (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux8]))
              (add norm 0 (by grind only [midpoint_add_sub]))
              (add norm 0 (by grind only [CliffordAlgebra.ι_mul_ι_mul_invOf_ι]))
              (add norm 0 (by grind only [star_sub]))
              (add norm 0 (by grind only [add_smul]))
              (add norm 0 (by grind only [smul_add]))
              (add norm 0 (by grind only [CliffordAlgebra.ι_mul_ι_mul_ι]))
              (add norm 0 (by grind only [sub_smul]))
              (add norm 0 (by grind only [WeakFEPair.Λ]))
              (add norm 0 (by grind only [realPart_apply_coe]))
              (add norm 0 (by grind only [CliffordAlgebra.ι_mul_ι_add_swap]))
              (add norm 0 (by grind only [tsirelson_inequality]))
              (add norm 0 (by grind only [imaginaryPart_apply_coe]))
              (add norm 0 (by grind only [AddCommGroup.modEq_sub_iff_add_modEq]))
              (add norm 0 (by grind only [realPart_add_I_smul_imaginaryPart]))
              (add norm 0 (by grind only [aux_add]))
              (add norm 0 (by grind only [smul_sub]))
              (add norm 0 (by grind only [selfAdjointPart]))
              (add norm 0 (by grind only [half_add_self]))
              (add norm 0 (by grind only [CliffordAlgebra.ι_mul_ι_comm]))
              (add safe 0 (by simp only [div_mul] at *))
              (add safe 0 (by simp only [div_div] at *))
              (add safe 0 (by simp only [mul_div] at *))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   (bound)
      _ = provingProb Astar (l + δ) - provingProb Astar l := by
          -- [L24.2] = p_s(l_k + δ) − p_s(l_k)
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * - hS2 hδ
          rw [hS2, hδ, smul_smul]
  have hp2 : ContDiff ℝ 2 (provingProb Astar) := by
    -- [aux] p_s is C² in the logits: the Taylor expansion of (2.3)→(2.4) needs it (the thesis uses it silently)
    -- [non-satp] Configuration A inferred by satp's policy fails (`satp?` did not finish within 2400 s and was terminated).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hM
    have hc : ∀ i : Fin H × Fin M, ContDiff ℝ 2 (fun l : Logits H M => l i) := by
      intro i
      exact (EuclideanSpace.proj i : Logits H M →L[ℝ] ℝ).contDiff
    have hpos : ∀ (l : Logits H M) (h : Fin H), (∑ m' : Fin M, Real.exp (l (h, m'))) ≠ 0 := by
      intro l h
      have h0 : 0 < ∑ m' : Fin M, Real.exp (l (h, m')) :=
        Finset.sum_pos (fun m' _ => Real.exp_pos _) ⟨⟨0, hM⟩, Finset.mem_univ _⟩
      exact h0.ne'
    have hs : ∀ h : Fin H, ContDiff ℝ 2 (fun l : Logits H M => ∑ m' : Fin M, Real.exp (l (h, m'))) :=
      fun h => ContDiff.sum fun m' _ => (hc (h, m')).exp
    have hsm : ∀ (h : Fin H) (m : Fin M), ContDiff ℝ 2 (fun l : Logits H M => softmax l h m) := by
      intro h m
      show ContDiff ℝ 2 (fun l : Logits H M => Real.exp (l (h, m)) / ∑ m' : Fin M, Real.exp (l (h, m')))
      exact ((hc (h, m)).exp).div (hs h) (fun l => hpos l h)
    have hpol : ∀ A : Arm H M, ContDiff ℝ 2 (fun l : Logits H M => policy l A) := by
      intro A
      have key : ∀ t : Finset (Fin H),
          ContDiff ℝ 2 (fun l : Logits H M => ∏ h ∈ t, softmax l h (A h)) := by
        intro t
        exact contDiff_prod fun h _ => hsm h (A h)
      exact key Finset.univ
    show ContDiff ℝ 2 (fun l : Logits H M => ∑ A ∈ Astar, policy l A)
    exact ContDiff.sum fun A _ => hpol A
  -- [aux, cite: differentiable_provingProb] p_s is differentiable, so ∇_l p_k is its gradient at l_k (used by L24.3)
  have hdp : Differentiable ℝ (provingProb Astar) := differentiable_provingProb Astar
  obtain ⟨ξ, hξ, hL243⟩ : ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      provingProb Astar (l + δ) - provingProb Astar l =
        (provingProb Astar l + @inner ℝ _ _ g δ +
            1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • δ)) ξ) -
          provingProb Astar l := by
    -- [L24.3] = (p_k + ∇_l p_kᵀ δ + ½ δᵀ (∇²_l p_s(ξ)) δ) − p_k   (Taylor expansion, for some ξ between l_k and l_k + δ; the point is l_k + ξ δ, and δᵀ ∇²_l p_s δ there is the second derivative of s ↦ p_s(l_k + s δ) at ξ)
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hp2 hg hdp
    have hA : ∀ s : ℝ, HasDerivAt (fun s : ℝ => l + s • δ) δ s := by
      intro s
      exact (((hasDerivAt_id' s).smul_const δ).const_add l).congr_deriv (one_smul ℝ δ)
    have hD : ∀ s : ℝ, HasDerivAt (fun s : ℝ => provingProb Astar (l + s • δ))
        (fderiv ℝ (provingProb Astar) (l + s • δ) δ) s := by
      intro s
      exact (hdp (l + s • δ)).hasFDerivAt.comp_hasDerivAt s (hA s)
    have hd0 : deriv (fun s : ℝ => provingProb Astar (l + s • δ)) 0 = inner ℝ g δ := by
      rw [(hD 0).deriv, zero_smul, add_zero, hg]
      all_goals simp only [gradient, InnerProductSpace.toDual_symm_apply]
    have hdf : Differentiable ℝ (fderiv ℝ (provingProb Astar)) := by
      have hc1 : ContDiff ℝ 1 (fderiv ℝ (provingProb Astar)) := by
        exact hp2.fderiv_right one_add_one_eq_two.le
      first
      | exact hc1.differentiable le_rfl
      | exact hc1.differentiable one_ne_zero
    have hd1 : Differentiable ℝ (fun s : ℝ => provingProb Astar (l + s • δ)) :=
      fun s => (hD s).differentiableAt
    have hd2 : Differentiable ℝ (deriv fun s : ℝ => provingProb Astar (l + s • δ)) := by
      have hdeq : (deriv fun s : ℝ => provingProb Astar (l + s • δ)) =
          fun s => fderiv ℝ (provingProb Astar) (l + s • δ) δ :=
        funext fun s => (hD s).deriv
      rw [hdeq]
      exact fun s => ((hdf (l + s • δ)).comp s (hA s).differentiableAt).clm_apply (differentiableAt_const δ)
    have key : ∀ f : ℝ → ℝ, Differentiable ℝ f → Differentiable ℝ (deriv f) →
        ∃ ξ ∈ Set.Ioo (0:ℝ) 1, f 1 - f 0 = deriv f 0 + 1 / 2 * deriv (deriv f) ξ := by
      intro f h1 h2
      have hF : ∀ x : ℝ, HasDerivAt (fun s => f s - s * deriv f 0 - (f 1 - f 0 - deriv f 0) * (s * s))
          (deriv f x - deriv f 0 - (f 1 - f 0 - deriv f 0) * (2 * x)) x := by
        intro x
        have hsq : HasDerivAt (fun s : ℝ => s * s) (2 * x) x := by
          exact ((hasDerivAt_id' x).mul (hasDerivAt_id' x)).congr_deriv (by ring)
        exact ((h1 x).hasDerivAt.sub (hasDerivAt_mul_const (deriv f 0))).sub
          (hsq.const_mul (f 1 - f 0 - deriv f 0))
      have hFc : ContinuousOn (fun s => f s - s * deriv f 0 - (f 1 - f 0 - deriv f 0) * (s * s))
          (Set.Icc 0 1) := fun x _ => (hF x).continuousAt.continuousWithinAt
      have hF01 : f 0 - 0 * deriv f 0 - (f 1 - f 0 - deriv f 0) * (0 * 0) =
          f 1 - 1 * deriv f 0 - (f 1 - f 0 - deriv f 0) * (1 * 1) := by ring
      obtain ⟨c, hc, hc0⟩ : ∃ c ∈ Set.Ioo (0:ℝ) 1,
          deriv f c - deriv f 0 - (f 1 - f 0 - deriv f 0) * (2 * c) = 0 :=
        exists_hasDerivAt_eq_zero (by norm_num) hFc hF01 (fun x _ => hF x)
      have hG : ∀ x : ℝ, HasDerivAt (fun s => deriv f s - s * (2 * (f 1 - f 0 - deriv f 0)))
          (deriv (deriv f) x - 2 * (f 1 - f 0 - deriv f 0)) x := fun x =>
        (h2 x).hasDerivAt.sub (hasDerivAt_mul_const (2 * (f 1 - f 0 - deriv f 0)))
      have hGc : ContinuousOn (fun s => deriv f s - s * (2 * (f 1 - f 0 - deriv f 0)))
          (Set.Icc 0 c) := fun x _ => (hG x).continuousAt.continuousWithinAt
      have hG0c : deriv f 0 - 0 * (2 * (f 1 - f 0 - deriv f 0)) =
          deriv f c - c * (2 * (f 1 - f 0 - deriv f 0)) := by
        linear_combination (-1 : ℝ) * hc0
      obtain ⟨ξ, hξ, hξ0⟩ : ∃ ξ ∈ Set.Ioo (0:ℝ) c,
          deriv (deriv f) ξ - 2 * (f 1 - f 0 - deriv f 0) = 0 :=
        exists_hasDerivAt_eq_zero hc.1 hGc hG0c (fun x _ => hG x)
      exact ⟨ξ, ⟨hξ.1, hξ.2.trans hc.2⟩, by linarith⟩
    obtain ⟨ξ, hξ, hξeq⟩ := key (fun s : ℝ => provingProb Astar (l + s • δ)) hd1 hd2
    refine ⟨ξ, hξ, ?_⟩
    have hξeq' : provingProb Astar (l + (1:ℝ) • δ) - provingProb Astar (l + (0:ℝ) • δ) =
        deriv (fun s : ℝ => provingProb Astar (l + s • δ)) 0 +
          1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • δ)) ξ := hξeq
    have e1 : provingProb Astar (l + (1:ℝ) • δ) = provingProb Astar (l + δ) := by rw [one_smul]
    have e0 : provingProb Astar (l + (0:ℝ) • δ) = provingProb Astar l := by rw [zero_smul, add_zero]
    linarith [hξeq', e1, e0, hd0]
  -- the chain (2.3)–(2.5)
  have h25 : provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l =
      @inner ℝ _ _ g ((α * (rs - rf)) • g) +
        1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • ((α * (rs - rf)) • g))) ξ :=
    calc provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l
        = provingProb Astar (l + δ) - provingProb Astar l := h23
      _ = (provingProb Astar l + @inner ℝ _ _ g δ +
              1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • δ)) ξ) -
            provingProb Astar l := hL243
      _ = @inner ℝ _ _ g ((α * (rs - rf)) • g) +
            1 / 2 * deriv (deriv fun s : ℝ =>
              provingProb Astar (l + s • ((α * (rs - rf)) • g))) ξ := by
          -- [L24.4] = ∇_l p_kᵀ (α Δ_r ∇_l p_k) + ½ (α Δ_r ∇_l p_k)ᵀ (∇²_l p_s(ξ)) (α Δ_r ∇_l p_k)
          -- [satp policy infer] satp's policy infers configuration A, and aesop proves this step with A.
          -- Proof body: the `satp?` "Try this" output, copied verbatim (indentation adjusted only).
          clear * - hδ
          aesop (config := {
              maxRuleApplications := 100
              maxRuleApplicationDepth := 10
              maxNormIterations := 320
              enableSimp := false
              useDefaultSimpSet := false
            })
              (add norm 100 (by norm_cast))
              (add norm 0 (by linarith))
              (add norm 0 (by nlinarith))
              (add norm 0 (by positivity))
              (add norm 0 (by omega))
              (add norm 1 (by push_neg))
              (add norm 0 (by bound))
              (add norm 0 (by ring_nf))
              (add norm 1 (by field_simp [*] at *))
              (add safe 100 (by ring))
              (add safe 100 (by field_simp))
              (add safe 100 (by norm_num))
              (add safe 100 (by interval_cases))
              (add safe 0 (by ext))
              (add safe 0 (by split))
              (add safe 100 (by rfl))
              (add safe 100 (by decide))
              (add safe 0 (by push_cast))
              (add safe 100 (by assumption_mod_cast))
              (add unsafe 10% (by exfalso))
              (add unsafe 90% (by norm_num [*] at *))
              (add norm 0 (by grind only [sub_smul]))
              (add norm 0 (by grind only [smul_add]))
              (add norm 0 (by grind only [smul_sub]))
              (add norm 0 (by grind only [mul_div_cancel]))
              (add norm 0 (by grind only [mul_div_cancel_left]))
              (add norm 0 (by grind only [add_smul]))
              (add norm 0 (by grind only [WeakFEPair.Λ]))
              (add norm 0 (by grind only [WeakFEPair.Λ₀_eq]))
              (add norm 0 (by grind only [smul_smul]))
              (add norm 0 (by grind only [Derivation.leibniz]))
              (add norm 0 (by grind only [div_mul]))
              (add norm 0 (by grind only [one_smul]))
              (add norm 0 (by grind only [two_smul]))
              (add norm 0 (by grind only [mul_div_cancel_right]))
              (add norm 0 (by grind only [MulAction]))
              (add norm 0 (by grind only [real_inner_smul_right]))
              (add norm 0 (by grind only [inner_]))
              (add norm 0 (by grind only [midpoint_add_sub]))
              (add norm 0 (by grind only [sub_div_sub_smul_slope_add_sub_div_sub_smul_slope]))
              (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux8]))
              (add norm 0 (by grind only [aux_sub]))
              (add norm 0 (by grind only [real_inner_smul_left]))
              (add norm 0 (by grind only [smul_eq_mul]))
              (add norm 0 (by grind only [InnerProductSpaceable.add_left_aux7]))
              (add norm 0 (by grind only [WeakFEPair.Λ₀]))
              (add norm 0 (by grind only [AddConstMapClass.map_sub_zsmul]))
              (add norm 0 (by grind only [skewAdjointPart]))
              (add norm 0 (by grind only [Convex.add_smul]))
              (add norm 0 (by grind only [neg_smul]))
              (add norm 0 (by grind only [smul_neg]))
              (add safe 0 (by simp only [div_div] at *))
              (add safe 0 (by simp only [mul_div] at *))
          -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
          --   (linarith)
  -- [cite: norm_gradient_expectedReward_le] Lemma 2.3 at l_k: ‖∇_l J_sparse(l_k)‖₂ ≤ √(HM) Δ_r p_k
  have hL23 := norm_gradient_expectedReward_le Astar rs rf hr l
  -- [cite: provingProb_deriv2_bound] the bounded Hessian of the softmax at the point l_k + ξ δ: |δᵀ ∇²_l p_s δ| ≤ (4H + 1) ‖δ‖₂²
  have hD2 := provingProb_deriv2_bound hM Astar l δ ξ
  -- [aux, cite: provingProb_nonneg] p_k ≥ 0, so both sides of Lemma 2.3's bound are nonnegative when squared (used by L24.8)
  have hpnn : 0 ≤ provingProb Astar l := provingProb_nonneg Astar l
  -- the chain (2.3)–(2.8)
  have h28 : provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ≤
      α * (rs - rf) * ((H : ℝ) * M * provingProb Astar l ^ 2) +
        1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * H + 1) * ((H : ℝ) * M * provingProb Astar l ^ 2) :=
    calc provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l
        = @inner ℝ _ _ g ((α * (rs - rf)) • g) +
            1 / 2 * deriv (deriv fun s : ℝ =>
              provingProb Astar (l + s • ((α * (rs - rf)) • g))) ξ := h25
      _ ≤ α * (rs - rf) * ‖g‖ ^ 2 + 1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * H + 1) * ‖g‖ ^ 2 := by
          -- [L24.5 + L24.6 merged into L24.7: the skeleton has no Hessian, so ‖∇²_l p_s(ξ)‖₂ and xᵀ Q x ≤ ‖Q‖₂ ‖x‖₂² have no Lean counterpart; with ‖∇²_l p_s‖₂ ≤ 4H + 1 they are provingProb_deriv2_bound] ≤ α Δ_r ‖∇_l p_k‖₂² + ½ α² Δ_r² ‖∇²_l p_s(ξ)‖₂ ‖∇_l p_k‖₂² = α Δ_r ‖∇_l p_k‖₂² + O(α² ‖∇_l p_k‖₂²), the O-term explicit with ‖∇²_l p_s(ξ)‖₂ ≤ 4H + 1   (the bounded Hessian of the softmax)
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * - hD2 hδ
          rw [hδ] at hD2
          have hn : ‖(α * (rs - rf)) • g‖ ^ 2 = α ^ 2 * (rs - rf) ^ 2 * ‖g‖ ^ 2 := by
            rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
            ring
          have key : ∀ x : ℝ, x ≤ (4 * (H : ℝ) + 1) * ‖(α * (rs - rf)) • g‖ ^ 2 →
              inner ℝ g ((α * (rs - rf)) • g) + 1 / 2 * x ≤
                α * (rs - rf) * ‖g‖ ^ 2 + 1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * (H : ℝ) + 1) * ‖g‖ ^ 2 := by
            intro x hx
            rw [hn] at hx
            rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
            linarith
          exact key _ ((le_abs_self _).trans hD2)
      _ ≤ α * (rs - rf) * ((H : ℝ) * M * provingProb Astar l ^ 2) +
            1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * H + 1) *
              ((H : ℝ) * M * provingProb Astar l ^ 2) := by
          -- [L24.8] ≤ α Δ_r (HM · p_k²) + O(α² (HM · p_k²)), the O-term explicit   (Lemma 2.3)
          -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
          -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
          -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
          -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
          clear * - hL23 hS2 hα hr hpnn
          have hd : 0 < rs - rf := sub_pos.mpr hr
          have hn : ‖(rs - rf) • g‖ = (rs - rf) * ‖g‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
          rw [hS2, hn] at hL23
          clear hS2
          have hg : ‖g‖ ≤ Real.sqrt ((H : ℝ) * M) * provingProb Astar l := by
            by_contra hcon
            push_neg at hcon
            linarith [mul_lt_mul_of_pos_left hcon hd]
          have h0 : 0 ≤ ‖g‖ := norm_nonneg _
          have hs : Real.sqrt ((H : ℝ) * M) * Real.sqrt ((H : ℝ) * M) = (H : ℝ) * M :=
            Real.mul_self_sqrt (by positivity)
          have hsq : ‖g‖ ^ 2 ≤ (H : ℝ) * M * provingProb Astar l ^ 2 := by
            calc ‖g‖ ^ 2 = ‖g‖ * ‖g‖ := sq _
              _ ≤ (Real.sqrt ((H : ℝ) * M) * provingProb Astar l) *
                    (Real.sqrt ((H : ℝ) * M) * provingProb Astar l) := mul_self_le_mul_self h0 hg
              _ = Real.sqrt ((H : ℝ) * M) * Real.sqrt ((H : ℝ) * M) * provingProb Astar l ^ 2 := by ring
              _ = (H : ℝ) * M * provingProb Astar l ^ 2 := by rw [hs]
          have hA : 0 ≤ α * (rs - rf) := mul_nonneg hα.le hd.le
          have hB : 0 ≤ 1 / 2 * α ^ 2 * (rs - rf) ^ 2 * (4 * (H : ℝ) + 1) := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left hsq hA) (mul_le_mul_of_nonneg_left hsq hB)
  have hL249 : |1 / 2 * deriv (deriv fun s : ℝ => provingProb Astar (l + s • ((α * (rs - rf)) • g))) ξ| ≤
      @inner ℝ _ _ g ((α * (rs - rf)) • g) := by
    -- [L24.9] In (2.5), for small α, the first term dominates the second   (read as |second| ≤ first; small α is α ≤ 1/((4H + 1) Δ_r))
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hD2 hδ hα hαle hr
    have hc : 0 < α * (rs - rf) := mul_pos hα (sub_pos.mpr hr)
    have hH : (0:ℝ) < 4 * (H:ℝ) + 1 := by positivity
    have hcle : (4 * (H:ℝ) + 1) * (α * (rs - rf)) ≤ 1 := by
      have h1 := (le_div_iff₀ (mul_pos hH (sub_pos.mpr hr))).mp hαle
      linarith
    have ha : inner ℝ δ δ = ‖δ‖ ^ 2 := real_inner_self_eq_norm_sq δ
    have hb : inner ℝ δ δ = α * (rs - rf) * inner ℝ g δ := by
      rw [hδ]; exact real_inner_smul_left _ _ _
    have e1 : inner ℝ g δ = α * (rs - rf) * inner ℝ g g := by
      rw [hδ]; exact real_inner_smul_right _ _ _
    have e2 : inner ℝ g g = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
    have hX : 0 ≤ inner ℝ g δ := by
      rw [e1, e2]; exact mul_nonneg hc.le (sq_nonneg _)
    have hK : (4 * (H:ℝ) + 1) * ‖δ‖ ^ 2 ≤ inner ℝ g δ := by
      rw [← ha, hb]
      have h4 := mul_le_mul_of_nonneg_right hcle hX
      linarith
    try rw [← hδ]
    refine le_trans ?_ (hD2.trans hK)
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by norm_num)
  have hL2410 : provingProb Astar l ≤ provingProb Astar (ascentStep Astar rs rf α l) := by
    -- [L24.10] so p_{k+1} ≥ p_k
    -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
    -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
    -- (indentation adjusted only).
    clear * - h25 hL249
    rw [sub_eq_iff_eq_add] at h25
    rw [abs_le] at hL249
    cases hL249
    linarith
  have hL2411 : 0 ≤ provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ∧
      provingProb Astar (ascentStep Astar rs rf α l) - provingProb Astar l ≤
        2 * α * ((H : ℝ) * M) * (rs - rf) * provingProb Astar l ^ 2 := by
    -- [L24.11] Thus, 0 ≤ p_{k+1} − p_k ≤ c · p_k², c ∈ O(α · HM · Δ_r), for a sufficiently small α   (here c = 2 α H M Δ_r and α ≤ 1/((4H + 1) Δ_r))
    -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
    -- Generative rule: no lemma rule of A that the search ran can be edited.
    -- bfsaesop also fails. The proof below was written by Opus 5.5 (a fresh Claude Code subagent that saw only this
    -- gap's goal, its thesis step, the statements of `Sec2`, and Lean's messages).
    clear * - hL2410 h28 hα hαle hr
    have hΔ : 0 < rs - rf := sub_pos.mpr hr
    have hK : 0 < (4 * (H : ℝ) + 1) * (rs - rf) := mul_pos (by positivity) hΔ
    have hαK : α * ((4 * (H : ℝ) + 1) * (rs - rf)) ≤ 1 := by
      exact (le_div_iff₀ hK).mp hαle
    have hX : 0 ≤ (H : ℝ) * M * provingProb Astar l ^ 2 := by positivity
    have hY : 0 ≤ α * (rs - rf) * ((H : ℝ) * M * provingProb Astar l ^ 2) :=
      mul_nonneg (mul_nonneg hα.le hΔ.le) hX
    have h1 := mul_le_mul_of_nonneg_right hαK hY
    refine ⟨sub_nonneg.mpr hL2410, ?_⟩
    linarith [h1, hY, h28]
  exact hL2411

end Sec2.DSP

end

-- ===== project/Sec2/DSP/Plateau.lean =====
section

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

end

-- ===== project/Sec2/DSP/RandomSearch.lean =====
section

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

end
