import Sec2.Basic

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
private lemma sum_exp_pos {M : ℕ} (x : Fin M → ℝ) (a : Fin M) :
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
    (sum_exp_pos (fun m' => l (h, m') + 0 * (if m' = m then 1 else 0)) a).ne'
  simp only [add_zero_mul_eq] at hq
  rw [sum_mul_ite_eq (fun m' => Real.exp (l (h, m'))) m] at hq
  rw [hfun]
  unfold softmax
  rw [div_mul_sub_div_eq _ _ _ _ (sum_exp_pos (fun m' => l (h, m')) a).ne']
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
