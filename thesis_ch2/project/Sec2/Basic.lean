import Mathlib

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
