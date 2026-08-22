
import Mathlib

/- Vendored verbatim from google-deepmind/formal-conjectures @ f564f8d7
(Apache-2.0): the `answer()` term elaborator (FormalConjectures/Util/Answer)
and `Real.nthRoot` (FormalConjecturesForMathlib/…/NthRoot). -/

/-- Indicates where the answer is in a problem statement. -/
syntax (name := Google.answer) "answer(" term ")" : term

namespace Google
open Lean Elab Term
/-- Indicates where the answer is in a problem statement. -/
@[term_elab answer]
def answerElab : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) => do
    mkSaveInfoAnnotation <$> postponeElabTerm (← `(by exact $a)) expectedType?
  | _ => Elab.throwUnsupportedSyntax
end Google

namespace Real
/-- `nthRoot n r` computes `ⁿ√r`; behaves as expected on negatives for odd `n`. -/
noncomputable def nthRoot (n : ℕ) (r : ℝ) : ℝ :=
  if Even n then r ^ (n⁻¹ : ℝ) else SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ)
end Real

open scoped Real
open scoped Nat
open scoped Topology
open scoped Polynomial


set_option maxHeartbeats 0

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  -- Step 3: Establish that 1 + x > 0 based on h₀
  have h_pos : 0 < 1 + x := by
    clear * - h₀
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
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.y_mul]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left']))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.x_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_right]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_left]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
      (add unsafe 50% (by nlinarith [Real.add_lt_add_iff_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_iff_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [lt_mul_iff_one_lt_left]))
      (add unsafe 50% (by nlinarith [lt_mul_of_one_lt_left']))
      (add unsafe 50% (by nlinarith [inv_lt_inv]))
      (add unsafe 50% (by nlinarith [Pell.Solution₁.x_mul_pos]))
      (add unsafe 50% (by nlinarith [lt_div_iff]))
      (add unsafe 50% (by nlinarith [div_lt_iff']))
      (add unsafe 50% (by nlinarith [mul_lt_iff_lt_one_right]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_right]))
      (add unsafe 50% (by nlinarith [lt_div_iff_mul_lt]))
      (add unsafe 50% (by nlinarith [div_lt_one]))
      (add unsafe 50% (by nlinarith [lt_div_iff']))
      (add unsafe 50% (by nlinarith [StrictConvexOn.slope_strict_mono_adjacent]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_logb]))
      (add unsafe 50% (by nlinarith [Real.logb_lt_logb_iff]))
      (add unsafe 50% (by nlinarith [inv_lt_iff_one_lt_mul]))
      (add unsafe 50% (by nlinarith [div_lt_iff_lt_mul]))
      (add unsafe 50% (by nlinarith [inv_lt_one]))
      (add unsafe 50% (by nlinarith [mul_inv_lt_iff_lt_mul]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [inv_lt_iff_one_lt_mul']))
      (add unsafe 50% (by nlinarith [inv_lt']))

  -- We proceed by induction on n. Since n > 0, we can use strong induction or standard induction starting from base case 1.
  -- Let's define a predicate P(m) = 1 + m*x <= (1+x)^m for m >= 1.
  -- Base Case: n = 1
  have h_base : 1 + (1 : ℕ) * x ≤ (1 + x) ^ (1 : ℕ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
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
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [Real.rpow_zero]))
      (add norm 0 (by grind only [AddChar.one_apply]))
      (add norm 0 (by rw [Nat.cast_one]))
      (add norm 0 (by rw [FractionalIdeal.absNorm_one]))
      (add norm 0 (by rw [Quaternion.coe_one]))
      (add norm 0 (by grind only [DiscreteValuationRing.addVal_uniformizer]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by grind only [MvPolynomial.C_1]))
      (add norm 0 (by grind only [NNReal.coe_one]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_apply_one]))
      (add norm 0 (by grind only [Real.one_rpow]))
      (add norm 0 (by grind only [TrivSqZeroExt.inl_one]))
      (add norm 0 (by grind only [ENNReal.coe_one]))
      (add norm 0 (by grind only [one_pow]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [HahnSeries.C_one]))
      (add norm 0 (by grind only [bernoulli_one]))
      (add norm 0 (by grind only [pow_zero]))
      (add norm 0 (by grind only [pow_one]))
      (add norm 0 (by grind only [IsLprojection.coe_one]))
      (add norm 0 (by grind only [ArithmeticFunction.one_apply]))
      (add norm 0 (by grind only [NumberField.Units.coe_one]))
      (add norm 0 (by grind only [Fin.val_one]))
      (add norm 0 (by grind only [ArithmeticFunction.vonMangoldt_apply_one]))
      (add norm 0 (by grind only [NormOneClass]))
      (add norm 0 (by grind only [MulRingSeminorm.apply_one]))
      (add norm 0 (by grind only [gronwallBound_ε0]))
      (add norm 0 (by grind only [Nat.factorial_zero]))
      (add norm 0 (by grind only [ArithmeticFunction.convolution_vonMangoldt_const_one]))
      (add unsafe 10% (by field_simp [Set.Icc.coe_one] at *))

  -- Inductive Step: Assume P(k) holds for some k >= 1, prove P(k+1).
  -- We will construct a helper lemma that assumes k >= 1 and P(k), and derives P(k+1).
  have h_inductive_step : ∀ (k : ℕ), 0 < k → (1 + ↑k * x ≤ (1 + x) ^ k) → (1 + ↑(k + 1) * x ≤ (1 + x) ^ (k + 1)) := by
    intro k hk_pos h_ineq_k
    -- Step 4: (1+x)^(k+1) = (1+x)^k * (1+x)
    have h_pow_expand : (1 + x) ^ (k + 1) = (1 + x) ^ k * (1 + x) := by
      clear * -
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 380
        maxNormIterations := 320
        maxGoals := 512
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by bound))
        (add norm 100 (by ring_nf at *))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 0 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by ext))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [mul_assoc]))
        (add norm 0 (by grind only [pow_succ]))
        (add norm 0 (by grind only [pow_succ']))
        (add norm 0 (by grind only [pow_add]))
        (add norm 0 (by grind only [mul_left_comm]))
        (add norm 0 (by grind only [mul_comm]))
        (add norm 0 (by grind only [mul_right_comm]))
        (add norm 0 (by grind only [Nat.pow_succ']))
        (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_param_pow_mul_iff]))
        (add norm 0 (by grind only [Nat.succ_mul]))
        (add norm 0 (by grind only [ppow_add]))
        (add norm 0 (by grind only [wittPolynomial_zmod_self]))
        (add norm 0 (by grind only [gold_pow_sub_gold_pow]))
        (add norm 0 (by grind only [Polynomial.derivative_pow_succ]))
        (add norm 0 (by grind only [IsNilpotent.pow_succ]))
        (add norm 0 (by grind only [Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one]))
        (add norm 0 (by grind only [Asymptotics.superpolynomialDecay_mul_param_pow_iff]))
        (add norm 0 (by grind only [PerfectClosure.mk_pow]))
        (add norm 0 (by grind only [Matrix.zpow_add_one]))
        (add norm 0 (by grind only [Nat.totient_prime_pow_succ]))
        (add norm 0 (by grind only [mul_pow]))
        (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
        (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux2]))
        (add norm 0 (by grind only [LinearMap.iterate_succ]))
        (add norm 0 (by grind only [Polynomial.expand_mul]))
        (add norm 0 (by grind only [WittVector.map_frobeniusPoly.key₂]))
        (add norm 0 (by grind only [WittVector.verschiebung_coeff_succ]))
        (add norm 0 (by grind only [WittVector.mul_polyOfInterest_aux4]))
        (add norm 0 (by grind only [LucasLehmer.X.ω]))
        (add norm 0 (by grind only [MvPolynomial.NewtonIdentities.esymm_to_weight]))
        (add norm 0 (by grind only [Nat.pow_succ]))
        (add norm 0 (by rw [mul_one]))

    -- Substitute into inequality
    have h_subst : (1 + x) ^ (k + 1) = (1 + x) ^ k * (1 + x) := by
      exact h_pow_expand

    -- Step 5: Use induction hypothesis h_ineq_k
    -- We want to show (1+x)^k * (1+x) >= 1 + (k+1)x
    -- From h_ineq_k: (1+x)^k >= 1 + kx
    -- Since 1+x > 0 (h_pos), we can multiply both sides of h_ineq_k by (1+x) preserving inequality.
    have h_mult : (1 + x) ^ k * (1 + x) ≥ (1 + ↑k * x) * (1 + x) := by
      -- Since (1+x) > 0, multiplication preserves order.
      -- h_ineq_k gives LHS_ge_rhs. Multiplying both by positive (1+x).
      clear * - h_ineq_k h_pos
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        maxGoals := 16
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
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
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [mul_le_mul_left']))
        (add norm 0 (by grind only [mul_le_mul_iff_left]))
        (add norm 0 (by grind only [mul_le_mul_right']))
        (add norm 0 (by grind only [mul_le_mul']))
        (add norm 0 (by grind only [mul_le_mul]))
        (add norm 0 (by grind only [mul_le_mul_iff_right]))
        (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
        (add norm 0 (by grind only [one_add_mul_le_pow]))
        (add norm 0 (by grind only [Real.BohrMollerup.f_add_nat_ge]))
        (add norm 0 (by grind only [SzemerediRegularity.m_add_one_div_m_le_one_add]))
        (add norm 0 (by grind only [Valuation.map_add_le]))
        (add norm 0 (by grind only [le_mul_left]))
        (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
        (add unsafe 50% (by nlinarith [mul_add_mul_le_mul_add_mul]))
        (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₅]))
        (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
        (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₁]))
        (add unsafe 50% (by nlinarith [le_trans]))
        (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
        (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₄]))
        (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₁]))
        (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₃]))
        (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
        (add unsafe 50% (by nlinarith [mul_le_mul_left]))
        (add unsafe 50% (by nlinarith [Ordnode.Valid'.merge_lemma]))
        (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₄]))
        (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
        (add unsafe 50% (by nlinarith [le_mul_of_one_le_right]))
        (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₂]))
        (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₂]))
        (add unsafe 50% (by nlinarith [Real.BohrMollerup.f_add_nat_le]))
        (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))

    -- Step 6 & 7: Expand (1 + kx)(1 + x)
    simp at *
    nlinarith [sq_nonneg (x : ℝ), sq_nonneg (k * x : ℝ)]

  -- Now apply the induction principle
  -- We have base case for n=1.
  -- We have step for k -> k+1 for any k>=1.
  -- We need to prove for arbitrary n >= 1.
  -- Using `nat.le_induction` or similar.
  -- Or simply use `induction` on n, but handling the 0 case which is excluded by h₁.
  match n with
  | 0 =>
    -- This branch is unreachable due to h₁ : 0 < n
    exfalso
    linarith

  | Nat.succ m =>
    -- We want to prove 1 + (m+1)*x <= (1+x)^(m+1)
    -- By applying the inductive step repeatedly.
    -- Let's use `induction` on m, starting from 0 (which corresponds to n=1).
    have h_all : ∀ (j : ℕ), 1 + ↑j * x ≤ (1 + x) ^ j := by
      intro j
      induction' j with k ih
      · -- Base case j=0: 1 + 0*x <= (1+x)^0 => 1 <= 1
        norm_num

      · -- Step j=k+1
        -- We need IH for k. But our inductive step lemma `h_inductive_step` requires k > 0?
        -- Actually, Bernoulli inequality holds for k=0 too?
        -- (1+x)^0 = 1. 1 + 0*x = 1. 1 <= 1. True.
        -- If k=0, next is j=1.
        -- Does h_inductive_step work for k=0?
        -- It required `0 < k`. So we can't use it directly from j=0 to j=1 if the lemma strictly needs k>0.
        -- However, we already proved h_base for n=1.
        -- Let's split cases or adjust the induction.
        -- Let's try a different induction approach that leverages `h_base` and `h_inductive_step`.
        -- We know P(1) is true.
        -- We know forall k>=1, P(k) -> P(k+1).
        -- Therefore forall n>=1, P(n).
        norm_cast at ih ⊢
        by_cases k_zero : k = 0
        · simp [k_zero]
        · push_neg at k_zero
          exact h_inductive_step k (Nat.pos_of_ne_zero k_zero) ih

    exact h_all (Nat.succ m)

  -- Refined Plan:
  -- Use `Nat.le_induction` on `n` with lower bound `1`.
  -- Or simply:
  -- have h_main : ∀ (m : ℕ), 1 ≤ m → 1 + ↑m * x ≤ (1 + x) ^ m := by
    -- intro m hm
    -- -- Strong induction or simple induction starting at 1
    -- classical
    -- have h_rec : ∀ (k : ℕ), 1 ≤ k → 1 + ↑k * x ≤ (1 + x) ^ k := by
      -- intro k hk_le_1
      -- -- Induction on k downwards? No, upwards.
      -- -- We can use `linarith` tactics often, but here we need specific lemmas.
      -- -- Let's use `omega` or `decide`? No, x is real.
      -- -- We can use the fact that we proved the step for all valid k.
      -- -- Base case is implicitly covered if we start from 1.
      -- -- Lean's `induction` typically starts at 0.
      -- -- Let's try to map our previous `h_inductive_step` and `h_base`.
      -- -- If k = 1, use h_base.
      -- -- If k > 1, k = j + 1 with j >= 1. Use h_inductive_step on j.
      -- cases' le_iff_exists_add.mpr hm with j hj_eq
      -- -- Here m = j + 1? No, `le_iff_exists_add` says ∃ j, m = i + j.
      -- -- If we want to go from 1 to m:
      -- -- Actually, the simplest way in Lean for "forall n>=1" given "base 1" and "step k->k+1"
      -- -- is to use `Nat.recOn` carefully or `StrongInduction`.
      -- -- Let's just use the helper `h_inductive_step` recursively.
      -- -- We can't easily recurse without an equation or match.
      -- suffices h_goal : 1 + ↑m * x ≤ (1 + x) ^ m by exact h_goal
      -- -- We use `linarith` if possible? No, involves powers.
      -- -- Let's try `apply_le_trans` chain manually using the proven lemmas.
      -- -- We can't loop in a tactic block easily without defining a recursive function.
      -- -- Alternative: Use `interval_cases`? No, domain is infinite.
      -- -- Let's rely on the `have` statements requested by the prompt format.
      -- -- The prompt asks for a series of `have` statements.
      -- -- I will construct the proof for the specific `n` using induction on `n`.
      -- -- Redoing the structure to fit `induction n`:
      -- revert m hm
      -- intro m hm_one
      -- have h_ind : ∀ (k : ℕ), 0 < k → 1 + ↑k * x ≤ (1 + x) ^ k := by
        -- intro k hk_pos
        -- have aux : ∀ (j : ℕ), 1 ≤ j → 1 + ↑j * x ≤ (1 + x) ^ j := by
          -- intro j hj_ge_1
          -- induction' j using Nat.strong_induction_on with j ih
          -- cases' j with j
          -- · -- j = 0, but hj_ge_1 says 1 <= 0, contradiction.
            -- linarith

          -- · -- j = succ j'
            -- cases' j with j''
            -- · -- j = 1
              -- norm_num at *
              -- -- Prove 1 + 1*x <= (1+x)^1
              -- have h_b : 1 + (1 : ℝ) * x ≤ (1 + x) ^ 1 := by
                -- norm_num
                -- linarith

              -- exact h_b

            -- · -- j = succ (succ j'') => j >= 2
              -- -- j = j'' + 2 ? No j = k+1 where k=j''.
              -- -- We have IH for all l < j. Specifically l = j-1 (which is j'').
              -- -- Note j'' >= 1 since j >= 2.
              -- have h_prev : 1 + ↑j'' * x ≤ (1 + x) ^ j'' := by
                -- apply ih
                -- omega

              -- have h_next : 1 + ↑j * x ≤ (1 + x) ^ j := by
                -- -- Apply inductive step from j'' to j''+1 (=j)
                -- -- We established h_inductive_step earlier which works for any k >= 1.
                -- -- j'' >= 1?
                -- have h_j'_pos : 1 ≤ j'' := by omega
                -- have h_j_pos : 0 < j := by omega
                -- -- Re-prove the step locally or use the global one if accessible?
                -- -- The global one `h_inductive_step` was proven above.
                -- -- But it might not be in scope if I nested it inside `all`.
                -- -- Let's reconstruct the logic briefly here.
                -- have h_pow_e : (1 + x) ^ j = (1 + x) ^ j'' * (1 + x) := by
                  -- rw [show j = j'' + 1 by omega]
                  -- ring_nf

                -- have h_inh_app : (1 + x) ^ j'' * (1 + x) ≥ (1 + ↑j'' * x) * (1 + x) := by
                  -- have h_mul_pos : 0 < 1 + x := h_pos
                  -- have h_hyp : 1 + ↑j'' * x ≤ (1 + x) ^ j'' := h_prev
                  -- calc
                    -- (1 + x) ^ j'' * (1 + x) ≥ (1 + ↑j'' * x) * (1 + x) := by
                      -- -- mul_le_mul_of_nonneg_right
                      -- have nonneg := h_mul_pos
                      -- simpa using mul_le_mul_of_nonneg_right h_hyp (le_of_lt h_mul_pos)

                    -- _ = (1 + ↑j'' * x) * (1 + x) := rfl

                -- have h_expand : (1 + ↑j'' * x) * (1 + x) = 1 + (↑j'' + 1 : ℝ) * x + ↑j'' * x ^ 2 := by
                  -- ring_nf

                -- have h_kx2_nonneg : 0 ≤ ↑j'' * x ^ 2 := by
                  -- have pos_j : 0 < ↑j'' := by exact_mod_cast h_j'_pos
                  -- have sq_nn : 0 ≤ x ^ 2 := sq_nonneg x
                  -- exact mul_nonneg (zero_le_of_lt pos_j) sq_nn

                -- have h_sum_ge : 1 + (↑j'' + 1 : ℝ) * x + ↑j'' * x ^ 2 ≥ 1 + (↑j'' + 1 : ℝ) * x := by
                  -- linarith

                -- have h_target : 1 + (↑j'' + 1 : ℝ) * x = 1 + ↑j * x := by
                  -- rw [show (↑j'' + 1 : ℝ) = ↑j by
                    -- norm_cast
                    -- omega]

                -- calc
                  -- (1 + x) ^ j = (1 + x) ^ j'' * (1 + x) := by rw [h_pow_e]
                  -- _ ≥ (1 + ↑j'' * x) * (1 + x) := h_inh_app
                  -- _ = 1 + (↑j'' + 1 : ℝ) * x + ↑j'' * x ^ 2 := by rw [h_expand]
                  -- _ ≥ 1 + (↑j'' + 1 : ℝ) * x := h_sum_ge
                  -- _ = 1 + ↑j * x := by rw [h_target]

              -- exact h_next

        -- exact aux m hm_one

      -- exact h_ind n h₁

  -- exact h_main n h₁
