import Sec2.SelfBound

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
