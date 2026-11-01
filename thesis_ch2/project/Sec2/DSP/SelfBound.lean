import Sec2.SelfBound
import Sec2.DSP.Basic

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
