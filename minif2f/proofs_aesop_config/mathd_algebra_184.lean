import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_184 (a b : NNReal) (h₀ : 0 < a ∧ 0 < b) (h₁ : a ^ 2 = 6 * b)
    (h₂ : a ^ 2 = 54 / b) : a = 3 * NNReal.sqrt 2 := by
  have h_step1 : (6 : NNReal) * b = (54 : NNReal) / b := by
    clear * - h₁ h₂
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 60
      enableUnfold := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 100 (by zify))
      (add norm 0 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 0 (by ext))
      (add norm 100 (by exfalso))
      (add norm 0 (by simp))
      (add norm 100 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 0 (by rfl))
      (add norm 0 (by decide))
      (add safe 1 (by norm_cast))
      (add safe 0 (by ring_nf))
      (add safe 0 (by split))
      (add safe 0 (by ring_nf at *))
      (add safe 1 (by push_cast))
      (add safe 0 (by assumption_mod_cast))
      (add unsafe 90% (by simp_all))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [Real.sq_sqrt]))
      (add norm 0 (by grind only [Real.sqrt_eq_rpow]))
      (add norm 0 (by grind only [PiLp.norm_eq_of_L2]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [WithLp.prod_norm_sq_eq_of_L2]))
      (add safe 0 (by simp_all [two_ne_zero]))
      (add unsafe 50% (by simp only [NumberField.mixedEmbedding.convexBodySumFactor]))
      (add unsafe 50% (by simp only [Real.sqrt]))
      (add unsafe 50% (by simp only [NNReal.sq_sqrt]))
      (add unsafe 50% (by simp only [Real.coe_sqrt]))
      (add unsafe 50% (by simp only [NNReal.rpow_two]))
      (add unsafe 50% (by simp only [NNReal.coe_ofNat]))
      (add unsafe 50% (by simp only [Complex.volume_ball]))
      (add unsafe 50% (by simp only [div_pow]))
      (add unsafe 50% (by simp_all [ENNReal.ofReal_pow]))
      (add unsafe 50% (by simp only [ENNReal.coe_pow]))
      (add unsafe 50% (by simp only [NNReal.sqrt_sq]))
      (add unsafe 50% (by simp only [NNReal.sqrt_eq_rpow]))
      (add unsafe 50% (by simp only [NNReal.coe_pow]))
      (add unsafe 50% (by simp only [ENNReal.coe_ofNat]))
      (add unsafe 50% (by simp only [sq_sub_sq]))
      (add unsafe 50% (by simp only [WithLp.prod_nnnorm_eq_of_L2]))
      (add unsafe 50% (by simp only [NumberField.mixedEmbedding.convexBodyLTFactor]))
      (add unsafe 50% (by simp only [NNReal.sqrt_mul]))
      (add unsafe 50% (by simp only [Matrix.frobenius_nnnorm_col]))
      (add unsafe 90% (by grind only [NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis]))
      (add unsafe 90% (by simp [sq_nonneg] at *))
      (add unsafe 50% (by simp only [PiLp.nnnorm_eq_of_L2]))
      (add unsafe 50% (by simp only [NNReal.sqrt]))
      (add unsafe 50% (by simp only [NNReal.coe_real_pi]))
      (add unsafe 50% (by simp only [sq_abs]))

  have h_step2 : (6 : NNReal) * b ^ 2 = (54 : NNReal) := by
    clear * - h_step1 h₀
    field_simp at *
    all_goals aesop
    field_simp [mul_comm, pow_two] at * <;> norm_cast

  have h_step3 : b ^ 2 = (9 : NNReal) := by
    clear * - h_step2
    rw [← NNReal.coe_inj] at *
    simp [mul_comm] at h_step2
    simp [← NNReal.coe_inj] at *
    nlinarith [pow_two (b : ℝ)]

  have h_step4 : b = (3 : NNReal) := by
    clear * - h_step3 h₀
    cases' b with b
    simp [← NNReal.coe_inj] at *
    any_goals nlinarith [sq_nonneg b]

  have h_step5 : a ^ 2 = (6 : NNReal) * (3 : NNReal) := by
    clear * - h₁ h_step4
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 60
      enableUnfold := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 100 (by zify))
      (add norm 0 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by interval_cases))
      (add norm 0 (by ext))
      (add norm 0 (by simp))
      (add norm 0 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 0 (by decide))
      (add safe 1 (by norm_cast))
      (add safe 0 (by ring_nf))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 0 (by rfl))
      (add safe 1 (by push_cast))
      (add safe 0 (by assumption_mod_cast))
      (add unsafe 90% (by simp_all))
      (add unsafe 50% (by norm_cast at *))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by solve_by_elim [Real.sq_sqrt]))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 100 (by rw [← mul_pow]))
      (add norm 0 (by grind only [WithLp.prod_norm_sq_eq_of_L2]))
      (add norm 100 (by rw [← ArithmeticFunction.moebius_sq]))
      (add norm 0 (by grind only [Real.sqrt_sq]))
      (add norm 0 (by grind only [PiLp.norm_eq_of_L2]))
      (add norm 0 (by grind only [PiLp.norm_sq_eq_of_L2]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [CoxeterSystem.simple_sq]))
      (add safe 0 (by simp_all [pow_two]))
      (add safe 100 (by simp [sq_sub_sq] at *))
      (add safe 0 (by simp_all [sq_pos_of_pos]))
      (add safe 0 (by nlinarith [Complex.volume_ball]))
      (add safe 0 (by simp_all [two_ne_zero]))
      (add safe 0 (by nlinarith [ENNReal.ofReal_pow]))
      (add unsafe 50% (by simp only [NNReal.rpow_two]))
      (add unsafe 50% (by simp only [Real.sqrt]))
      (add unsafe 50% (by simp only [NNReal.sq_sqrt]))
      (add unsafe 50% (by simp only [sq_abs]))
      (add unsafe 50% (by simp only [NumberField.mixedEmbedding.convexBodySumFactor]))
      (add unsafe 50% (by simp only [Real.coe_sqrt]))
      (add unsafe 90% (by grind only [Real.rpow_two]))
      (add unsafe 90% (by simp [sq_nonneg] at *))
      (add unsafe 50% (by simp only [NNReal.sqrt_sq]))
      (add unsafe 50% (by simp only [NNReal.coe_pow]))
      (add unsafe 50% (by simp only [NNReal.coe_ofNat]))
      (add unsafe 50% (by simp only [ENNReal.coe_pow]))
      (add unsafe 50% (by simp only [NumberField.mixedEmbedding.convexBodyLTFactor]))
      (add unsafe 10% (by positivity [gaussSum_sq]))
      (add unsafe 50% (by simp only [NNReal.sqrt_eq_rpow]))

  have h_step6 : a ^ 2 = (18 : NNReal) := by
    clear * - h_step5
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 30
      maxGoals := 64
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 100 (by zify))
      (add norm 0 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by interval_cases))
      (add norm 0 (by ext))
      (add norm 0 (by simp))
      (add norm 0 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 0 (by decide))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 0 (by rfl))
      (add safe 1 (by push_cast))
      (add safe 0 (by assumption_mod_cast))
      (add unsafe 50% (by norm_cast))
      (add unsafe 10% (by ring_nf))
      (add unsafe 90% (by simp_all))
      (add unsafe 50% (by norm_cast at *))
      (add norm 0 (by grind only [sq_add_sq_mul]))
      (add norm 0 (by grind only [EuclideanSpace.norm_eq]))
      (add norm 0 (by solve_by_elim [Real.sq_sqrt]))
      (add norm 0 (by grind only [sq_eq_sq]))
      (add norm 0 (by grind only [sq_eq_one_iff]))
      (add norm 0 (by grind only [euler_four_squares]))
      (add norm 100 (by rw [← mul_pow]))
      (add norm 0 (by grind only [WithLp.prod_norm_sq_eq_of_L2]))
      (add norm 0 (by grind only [PiLp.norm_eq_of_L2]))
      (add norm 1 (by simp_all [zero_lt_two]))
      (add safe 0 (by simp_all [pow_two]))
      (add safe 0 (by simp_all [Real.rpow_two]))
      (add safe 0 (by simp_all [two_ne_zero]))
      (add safe 0 (by solve_by_elim [Real.sqrt_sq]))
      (add safe 100 (by simp [QuaternionGroup.xa_sq] at *))
      (add safe 100 (by simp [CharTwo.sum_sq] at *))
      (add safe 100 (by simp [Pell.Solution₁.prop_x] at *))
      (add unsafe 10% (by rw [ArithmeticFunction.moebius_sq]))
      (add unsafe 50% (by unfold CoxeterSystem.simple_sq))
      (add unsafe 10% (by push_cast [sq_sub_sq] at *))
      (add unsafe 10% (by push_cast [sq_pos_of_pos] at *))
      (add unsafe 50% (by simp only [NNReal.rpow_two]))
      (add unsafe 90% (by simp [sq_abs] at *))
      (add unsafe 90% (by norm_num [gaussSum_sq] at *))
      (add unsafe 90% (by simp [sq_nonneg] at *))
      (add unsafe 10% (by rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
      (add unsafe 10% (by rw [quadraticChar_sq_one]))
      (add unsafe 10% (by rw [quadraticChar_sq_one']))
      (add unsafe 50% (by unfold MulChar.IsQuadratic.sq_eq_one))
      (add unsafe 90% (by unfold sq_lt_sq))
      (add unsafe 90% (by norm_num [ENNReal.rpow_two] at *))
      (add unsafe 10% (by field_simp [div_pow] at *))

  have h_step7 : a = NNReal.sqrt (18 : NNReal) := by
    clear * - h_step6 h₀
    have ha : 0 < a := h₀.1
    have h : a ^ 2 = (18 : NNReal) := h_step6
    simp [← h]

  have h_step8 : a = NNReal.sqrt ((9 : NNReal) * (2 : NNReal)) := by
    clear * - h_step7
    aesop (config := {
      maxRuleApplicationDepth := 20
      maxNormIterations := 60
      maxGoals := 1024
      useSimpAll := false
      enableUnfold := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_num))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by push_neg))
      (add norm 0 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by interval_cases))
      (add norm 0 (by ext))
      (add norm 0 (by simp))
      (add norm 0 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 0 (by decide))
      (add safe 1 (by norm_cast))
      (add safe 1 (by zify))
      (add safe 0 (by ring_nf))
      (add safe 0 (by split))
      (add safe 1 (by exfalso))
      (add safe 0 (by rfl))
      (add safe 1 (by push_cast))
      (add safe 0 (by assumption_mod_cast))
      (add unsafe 50% (by abel))
      (add unsafe 90% (by simp_all))
      (add unsafe 50% (by norm_num [*] at *))
      (add unsafe 50% (by norm_cast at *))
      (add norm 1 (by rw [← NumberField.mixedEmbedding.convexBodySumFactor]))
      (add norm 1 (by rw [PiLp.norm_eq_of_L2]))
      (add norm 0 (by solve_by_elim [Real.sqrt_sq]))
      (add norm 1 (by rw [EuclideanSpace.norm_eq]))
      (add norm 0 (by grind only [WithLp.prod_norm_eq_of_L2]))
      (add norm 1 (by rw [← Real.sqrt_eq_iff_sq_eq]))
      (add norm 1 (by rw [PiLp.nnnorm_eq_of_L2]))
      (add norm 0 (by grind only [Real.sqrt_mul]))
      (add safe 0 (by push_cast [Real.sq_sqrt] at *))
      (add safe 0 (by simp_all [pow_two]))
      (add safe 1 (by rw [Real.sqrt_eq_rpow]))
      (add safe 1 (by rw [← Nat.sqrt_eq']))
      (add safe 0 (by simp_all [two_ne_zero]))
      (add unsafe 50% (by simp only [Real.sqrt]))
      (add unsafe 50% (by simp only [Real.coe_sqrt]))
      (add unsafe 50% (by simp only [NNReal.rpow_two]))
      (add unsafe 50% (by simp only [NNReal.sq_sqrt]))
      (add unsafe 50% (by simp only [NNReal.sqrt_eq_rpow]))
      (add unsafe 10% (by apply NNReal.coe_ofNat))
      (add unsafe 50% (by simp only [NNReal.sqrt_sq]))
      (add unsafe 50% (by simp only [NNReal.coe_two]))
      (add unsafe 50% (by simp only [WithLp.prod_nnnorm_eq_of_L2]))
      (add unsafe 50% (by simp only [ENNReal.coe_ofNat]))
      (add unsafe 50% (by simp only [NumberField.mixedEmbedding.convexBodyLTFactor]))
      (add unsafe 50% (by simp only [NNReal.sqrt_mul]))
      (add unsafe 50% (by simp only [NNReal.sqrt]))
      (add unsafe 50% (by simp only [NNReal.coe_pow]))
      (add unsafe 90% (by grind only [Real.rpow_two]))
      (add unsafe 10% (by positivity [Complex.volume_ball]))
      (add unsafe 10% (by apply Matrix.frobenius_nnnorm_col))
      (add unsafe 50% (by simp only [NNReal.coe_real_pi]))
      (add unsafe 50% (by simp only [NumberField.mixedEmbedding.convexBodyLT'Factor]))

  have h_step9 : a = NNReal.sqrt (9 : NNReal) * NNReal.sqrt (2 : NNReal) := by
    clear * - h_step8
    simp [h_step8, ← NNReal.sqrt_mul]

  have h_step10 : a = (3 : NNReal) * NNReal.sqrt (2 : NNReal) := by
    clear * - h_step9
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 60
      maxGoals := 1024
      useSimpAll := false
      enableUnfold := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 0 (by gcongr))
      (add norm 0 (by bound))
      (add norm 0 (by interval_cases))
      (add norm 0 (by ext))
      (add norm 0 (by simp))
      (add norm 0 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 0 (by decide))
      (add norm 100 (by push_cast))
      (add safe 1 (by norm_cast))
      (add safe 1 (by zify))
      (add safe 0 (by ring_nf))
      (add safe 0 (by split))
      (add safe 1 (by exfalso))
      (add safe 0 (by rfl))
      (add safe 0 (by assumption_mod_cast))
      (add unsafe 90% (by simp_all))
      (add unsafe 50% (by norm_num [*] at *))
      (add unsafe 50% (by norm_cast at *))
      (add unsafe 50% (by simp only [Real.coe_sqrt]))
      (add unsafe 50% (by simp only [NNReal.sq_sqrt]))
      (add unsafe 50% (by simp only [NNReal.sqrt_eq_rpow]))
      (add unsafe 50% (by simp only [NNReal.sqrt_sq]))
      (add unsafe 50% (by simp only [NNReal.sqrt_mul]))
      (add unsafe 50% (by simp only [NNReal.sqrt]))
      (add unsafe 50% (by simp only [NNReal.coe_ofNat]))
      (add unsafe 50% (by simp only [WithLp.prod_nnnorm_eq_of_L2]))
      (add unsafe 50% (by simp only [NNReal.coe_mul]))
      (add unsafe 50% (by simp only [NNReal.coe_two]))
      (add unsafe 50% (by simp only [Real.sqrt]))
      (add unsafe 50% (by simp only [NumberField.mixedEmbedding.convexBodyLTFactor]))
      (add unsafe 50% (by simp only [NNReal.coe_pow]))
      (add unsafe 50% (by simp only [ENNReal.coe_ofNat]))
      (add unsafe 50% (by simp only [NumberField.mixedEmbedding.convexBodySumFactor]))
      (add unsafe 50% (by simp only [NNReal.coe_rpow]))
      (add unsafe 50% (by simp only [NNReal.mul_rpow]))
      (add unsafe 50% (by simp only [NNReal.rpow_two]))
      (add unsafe 50% (by simp only [Quaternion.nnnorm_coe]))
      (add unsafe 50% (by simp only [ENNReal.coe_pow]))
      (add unsafe 50% (by simp only [NumberField.mixedEmbedding.convexBodyLT'Factor]))
      (add unsafe 50% (by simp only [PiLp.nnnorm_eq_of_L2]))
      (add unsafe 50% (by simp only [NNReal.val_eq_coe]))
      (add unsafe 50% (by simp only [NNReal.coe_real_pi]))
      (add unsafe 50% (by simp only [Quaternion.nnnorm_star]))
      (add unsafe 50% (by simp only [NNReal.sqrt_inv]))
      (add unsafe 50% (by simp only [Matrix.frobenius_nnnorm_def]))
      (add unsafe 50% (by simp only [NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis]))
      (add unsafe 50% (by simp only [Matrix.frobenius_nnnorm_col]))
      (add unsafe 50% (by simp only [norm_toNNReal']))
      (add unsafe 50% (by simp only [NNReal.norm_eq]))
      (add unsafe 90% (by grind only [Real.toNNReal_ofNat]))

  exact h_step10
