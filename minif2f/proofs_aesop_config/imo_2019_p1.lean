import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem imo_2019_p1 (f : ℤ → ℤ) :
  (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔ ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  constructor
  · intro h_eq
    let c := f 0
    have h_step3 : f (f 0) = 3 * c := by
      clear * - h_eq
      have h0 := h_eq 0 0
      simp_all [c] <;> omega

    have h_step4 : ∀ a, f (2 * a) + 2 * c = f (f a) := by
      clear * - h_eq
      aesop (config := {
        maxRuleApplications := 400
        maxRuleApplicationDepth := 120
        maxNormIterations := 800
        maxGoals := 128
        }) (rule_sets := [-builtin])
        (add norm 100 (by ring))
        (add norm 100 (by field_simp))
        (add norm 100 (by norm_num))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 100 (by abel))
        (add norm 100 (by zify))
        (add norm 100 (by bound))
        (add norm 100 (by interval_cases))
        (add norm 100 (by ext))
        (add norm 100 (by exfalso))
        (add norm 100 (by ring_nf at *))
        (add norm 100 (by norm_num [*] at *))
        (add norm 100 (by norm_cast at *))
        (add norm 100 (by rfl))
        (add norm 100 (by push_cast))
        (add safe 0 (by omega))
        (add safe 0 (by ring_nf))
        (add safe 0 (by split))
        (add safe 0 (by simp_all))
        (add safe 0 (by field_simp [*] at *))
        (add safe 0 (by assumption_mod_cast))
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [Quaternion.self_add_star]))
        (add norm 0 (by grind only [mul_two]))
        (add norm 1 (by norm_num [CharTwo.two_eq_zero] at *))
        (add norm 1 (by norm_num [Quaternion.star_add_self] at *))
        (add norm 1 (by norm_num [Polynomial.natTrailingDegree_mul_mirror] at *))
        (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
        (add norm 1 (by norm_num [Nat.cast_descFactorial_two] at *))
        (add norm 1 (by norm_num [Ring.multichoose_two] at *))
        (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
        (add norm 100 (by rw [Polynomial.natDegree_mul_mirror]))
        (add norm 100 (by rw [← ack_two]))
        (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
        (add norm 0 (by grind only [Nat.cast_ofNat]))
        (add norm 0 (by grind only [zero_lt_two]))
        (add norm 0 (by grind only [Nat.two_mul]))
        (add norm 100 (by simp only [one_add_one_eq_two]))
        (add safe 0 (by simp_all [two_ne_zero]))
        (add safe 0 (by simp_all [Nat.cast_two]))
        (add safe 0 (by simp_all [pow_two]))
        (add safe 0 (by grind only [Quaternion.self_add_star']))
        (add safe 0 (by grind only [Quaternion.star_add_self']))
        (add safe 0 (by norm_num [Zsqrtd.divides_sq_eq_zero_z] at *))
        (add safe 1 (by rw [Int.sq_add_sq_of_two_mul_sq_add_sq]))
        (add safe 0 (by simp_all [Int.sq_of_gcd_eq_one]))
        (add unsafe 50% (by simp only [Int.cast_two]))
        (add unsafe 50% (by simp [Int.cast_ofNat] at *))
        (add unsafe 50% (by simp_rw [Int.emod_zero]))
        (add unsafe 90% (by grind only [Nat.factorial_two]))
        (add unsafe 90% (by grind only [zpow_two]))
        (add unsafe 50% (by simp only [sq_ne_two_fin_zmod_four]))
        (add unsafe 10% (by apply Real.sin_two_mul))

    have h_step5 : ∀ b, c + 2 * f b = f (f b) := by
      clear * - h_eq
      intro b
      have h := h_eq 0 b
      aesop  (add simp [c])

    have h_step6 : ∀ a, f (2 * a) + 2 * c = c + 2 * f a := by
      clear * - h_step4 h_step5
      aesop (config := {
        maxRuleApplications := 400
        maxRuleApplicationDepth := 120
        maxNormIterations := 800
        maxGoals := 128
        enableUnfold := false
        }) (rule_sets := [-builtin])
        (add norm 100 (by ring))
        (add norm 100 (by field_simp))
        (add norm 100 (by norm_num))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 100 (by nlinarith))
        (add norm 100 (by abel))
        (add norm 100 (by push_neg))
        (add norm 100 (by zify))
        (add norm 100 (by bound))
        (add norm 100 (by interval_cases))
        (add norm 100 (by ext))
        (add norm 100 (by split))
        (add norm 100 (by exfalso))
        (add norm 100 (by ring_nf at *))
        (add norm 1 (by field_simp [*] at *))
        (add norm 100 (by norm_num [*] at *))
        (add norm 100 (by norm_cast at *))
        (add norm 100 (by decide))
        (add norm 100 (by push_cast))
        (add norm 100 (by assumption_mod_cast))
        (add safe 0 (by omega))
        (add safe 0 (by simp_all))
        (add safe 0 (by rfl))
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [Quaternion.self_add_star]))
        (add norm 0 (by grind only [mul_two]))
        (add norm 0 (by grind only [Quaternion.star_add_self]))
        (add norm 0 (by grind only [Quaternion.star_add_self']))
        (add norm 100 (by simp only [mul_comm] at *))
        (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
        (add norm 100 (by simp only [mul_left_comm] at *))
        (add norm 0 (by grind only [Quaternion.self_add_star']))
        (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
        (add norm 100 (by rw [← ack_two]))
        (add norm 100 (by simp only [mul_right_comm] at *))
        (add norm 100 (by simp only [mul_assoc] at *))
        (add norm 0 (by grind only [mul_add_mul]))
        (add norm 0 (by grind only [Int.cast_ofNat]))
        (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
        (add norm 100 (by simp only [one_add_one_eq_two]))
        (add norm 100 (by simp only [Nat.cast_two]))
        (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
        (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
        (add norm 0 (by grind only [Ring.multichoose_two]))
        (add norm 0 (by grind only [Nat.two_mul]))
        (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
        (add norm 0 (by grind only [QuaternionAlgebra.self_add_star']))
        (add norm 1 (by norm_num [CharTwo.two_eq_zero] at *))
        (add safe 1 (by rw [Int.sq_add_sq_of_two_mul_sq_add_sq]))
        (add safe 0 (by simp_all [two_ne_zero]))
        (add safe 0 (by simp_all [pow_two]))
        (add unsafe 90% (by grind only [Int.cast_two]))
        (add unsafe 90% (by grind only [Real.sin_two_mul]))
        (add unsafe 90% (by grind only [zpow_two]))
        (add unsafe 50% (by simp_all [two_ne_zero']))

    have h_step9 : ∀ a, f (2 * a) = 2 * f a - c := by
      clear * - h_step6
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 120
        maxNormIterations := 60
        maxGoals := 128
        enableUnfold := false
        }) (rule_sets := [-builtin])
        (add norm 100 (by ring))
        (add norm 100 (by field_simp))
        (add norm 100 (by norm_num))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 100 (by abel))
        (add norm 100 (by zify))
        (add norm 100 (by bound))
        (add norm 100 (by interval_cases))
        (add norm 100 (by ext))
        (add norm 100 (by split))
        (add norm 100 (by exfalso))
        (add norm 100 (by ring_nf at *))
        (add norm 1 (by field_simp [*] at *))
        (add norm 100 (by norm_num [*] at *))
        (add norm 100 (by norm_cast at *))
        (add norm 100 (by rfl))
        (add norm 100 (by decide))
        (add norm 100 (by push_cast))
        (add norm 100 (by assumption_mod_cast))
        (add safe 1 (by ring_nf))
        (add safe 0 (by simp_all))
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [mul_two]))
        (add norm 0 (by grind only [Quaternion.star_add_self]))
        (add norm 0 (by grind only [Quaternion.self_add_star]))
        (add norm 0 (by grind only [add_halves]))
        (add norm 100 (by simp only [Real.two_mul_arctan_sub_pi]))
        (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
        (add norm 100 (by simp only [Real.sin_two_mul]))
        (add norm 0 (by grind only [Quaternion.star_add_self']))
        (add norm 0 (by grind only [mul_div_cancel_left]))
        (add norm 0 (by grind only [div_eq_iff_eq_mul]))
        (add norm 100 (by simp only [one_add_one_eq_two]))
        (add norm 0 (by grind only [half_add_self]))
        (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
        (add norm 0 (by grind only [sub_half]))
        (add norm 0 (by grind only [add_halves']))
        (add norm 100 (by simp only [Nat.cast_two]))
        (add norm 100 (by simp only [Real.two_mul_arctan]))
        (add norm 0 (by grind only [mul_div_cancel_right]))
        (add norm 100 (by rw [← ack_two]))
        (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
        (add norm 0 (by grind only [Quaternion.self_add_star']))
        (add norm 1 (by rw [InnerProductSpaceable.add_left_aux4]))
        (add norm 100 (by simp only [Nat.cast_descFactorial_two]))
        (add safe 100 (by rw [two_ne_zero'] at *))
        (add safe 0 (by simp_all [two_ne_zero]))
        (add safe 0 (by simp_all [pow_two]))
        (add unsafe 90% (by grind only [Int.cast_two]))
        (add unsafe 50% (by simp_all [div_mul]))
        (add unsafe 90% (by grind only [zpow_two]))
        (add unsafe 90% (by grind only [Real.two_mul_arctan_add_pi]))
        (add unsafe 50% (by simp_all [div_div]))

    have h_step10 : ∀ x, f (f x) = 2 * f x + c := by
      clear * - h_step5
      aesop (config := {
        maxRuleApplications := 400
        maxRuleApplicationDepth := 120
        maxNormIterations := 800
        maxGoals := 128
        enableUnfold := false
        }) (rule_sets := [-builtin])
        (add norm 100 (by ring))
        (add norm 100 (by field_simp))
        (add norm 100 (by norm_num))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 100 (by abel))
        (add norm 100 (by zify))
        (add norm 100 (by bound))
        (add norm 100 (by interval_cases))
        (add norm 100 (by ext))
        (add norm 100 (by split))
        (add norm 100 (by exfalso))
        (add norm 0 (by simp_all))
        (add norm 100 (by ring_nf at *))
        (add norm 1 (by field_simp [*] at *))
        (add norm 100 (by norm_num [*] at *))
        (add norm 100 (by norm_cast at *))
        (add norm 100 (by rfl))
        (add norm 100 (by push_cast))
        (add norm 100 (by assumption_mod_cast))
        (add safe 1 (by ring_nf))
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [mul_two]))
        (add norm 0 (by grind only [Quaternion.self_add_star]))
        (add norm 1 (by norm_num [Quaternion.star_add_self] at *))
        (add norm 0 (by grind only [Quaternion.star_add_self']))
        (add norm 100 (by rw [← ack_two]))
        (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
        (add norm 100 (by simp only [one_add_one_eq_two]))
        (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
        (add norm 1 (by norm_num [Ring.multichoose_two] at *))
        (add norm 0 (by grind only [Nat.two_mul]))
        (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
        (add norm 0 (by grind only [Quaternion.self_add_star']))
        (add norm 100 (by simp only [Nat.cast_two]))
        (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
        (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
        (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
        (add norm 100 (by simp only [CharTwo.two_eq_zero]))
        (add norm 1 (by norm_num [Nat.cast_descFactorial_two] at *))
        (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
        (add norm 100 (by simp only [mul_comm] at *))
        (add norm 0 (by grind only [Int.cast_ofNat]))
        (add norm 0 (by grind only [QuaternionAlgebra.self_add_star']))
        (add norm 100 (by rw [Polynomial.natDegree_mul_mirror]))
        (add safe 0 (by simp_all [two_ne_zero]))
        (add safe 100 (by rw [two_ne_zero'] at *))
        (add unsafe 90% (by grind only [Int.cast_two]))
        (add unsafe 10% (by apply Real.sin_two_mul))
        (add unsafe 90% (by grind only [zpow_two]))
        (add unsafe 10% (by apply Real.two_mul_arctan_sub_pi))
        (add unsafe 10% (by apply Complex.sin_two_mul))
        (add unsafe 90% (by grind only [Nat.factorial_two]))

    have h_step14 : ∀ a b, 2 * f (a + b) = 2 * f a + 2 * f b - 2 * c := by
      clear * - h_eq h_step9 h_step10
      aesop (config := {
        maxRuleApplications := 400
        maxRuleApplicationDepth := 10
        maxNormIterations := 800
        maxGoals := 128
        enableSimp := false
        enableUnfold := false
        })
        (add norm 100 (by ring))
        (add norm 100 (by field_simp))
        (add norm 100 (by norm_num))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 100 (by abel))
        (add norm 100 (by zify))
        (add norm 100 (by bound))
        (add norm 100 (by interval_cases))
        (add norm 100 (by ext))
        (add norm 100 (by split))
        (add norm 100 (by exfalso))
        (add norm 100 (by ring_nf at *))
        (add norm 100 (by norm_num [*] at *))
        (add norm 100 (by norm_cast at *))
        (add norm 100 (by rfl))
        (add norm 100 (by decide))
        (add norm 100 (by push_cast))
        (add norm 100 (by assumption_mod_cast))
        (add safe 1 (by ring_nf))
        (add safe 0 (by simp_all))
        (add safe 0 (by field_simp [*] at *))
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [Quaternion.star_add_self]))
        (add norm 0 (by grind only [Quaternion.self_add_star]))
        (add norm 0 (by grind only [mul_two]))
        (add norm 0 (by grind only [Quaternion.star_add_self']))
        (add norm 0 (by grind only [half_add_self]))
        (add norm 0 (by grind only [Quaternion.self_add_star']))
        (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
        (add norm 0 (by grind only [add_halves]))
        (add norm 0 (by grind only [div_mul]))
        (add norm 0 (by grind only [Int.emod_add_ediv]))
        (add norm 0 (by grind only [mul_add_mul]))
        (add norm 0 (by grind only [two_ne_zero']))
        (add norm 0 (by grind only [mul_div_cancel_right]))
        (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
        (add norm 0 (by grind only [QuaternionAlgebra.star_add_self']))
        (add norm 0 (by grind only [add_halves']))
        (add norm 100 (by simp only [mul_comm] at *))
        (add norm 0 (by grind only [QuaternionAlgebra.self_add_star']))
        (add norm 100 (by simp only [Real.two_mul_arctan_sub_pi]))
        (add norm 0 (by grind only [add_self_div_two]))
        (add norm 100 (by simp only [mul_right_comm] at *))
        (add norm 0 (by grind only [div_eq_iff_eq_mul]))
        (add norm 0 (by grind only [mul_div_cancel_left]))
        (add norm 0 (by grind only [eq_div_iff_mul_eq']))
        (add norm 0 (by grind only [div_div]))
        (add norm 1 (by rw [QuaternionGroup.xa_mul_xa]))
        (add norm 0 (by grind only [jacobiTheta_two_add]))
        (add norm 0 (by grind only [mul_div]))
        (add norm 100 (by rw [← ack_two]))
        (add safe 1 (by rw [Int.sq_add_sq_of_two_mul_sq_add_sq]))
        (add unsafe 90% (by grind only [Real.sin_two_mul]))

    have h_step15 : ∀ a b, f (a + b) = f a + f b - c := by
      clear * - h_step14
      aesop (config := {
        maxRuleApplications := 400
        maxRuleApplicationDepth := 120
        maxNormIterations := 30
        maxGoals := 128
        enableUnfold := false
        })
        (add norm 100 (by ring))
        (add norm 100 (by field_simp))
        (add norm 100 (by norm_num))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 100 (by abel))
        (add norm 100 (by zify))
        (add norm 100 (by bound))
        (add norm 100 (by interval_cases))
        (add norm 100 (by ext))
        (add norm 100 (by exfalso))
        (add norm 100 (by ring_nf at *))
        (add norm 100 (by norm_num [*] at *))
        (add norm 100 (by norm_cast at *))
        (add norm 100 (by rfl))
        (add norm 100 (by push_cast))
        (add norm 100 (by assumption_mod_cast))
        (add safe 1 (by ring_nf))
        (add safe 0 (by split))
        (add safe 0 (by simp_all))
        (add safe 0 (by field_simp [*] at *))
        (add norm 100 (by simp only [mul_comm] at *))
        (add norm 0 (by grind only [two_mul]))
        (add norm 100 (by simp only [mul_right_comm] at *))
        (add norm 100 (by simp only [mul_left_comm] at *))
        (add norm 100 (by simp only [mul_assoc] at *))
        (add norm 1 (by rw [div_mul]))
        (add norm 0 (by grind only [mul_div]))
        (add norm 0 (by grind only [Int.emod_add_ediv]))
        (add norm 0 (by grind only [div_eq_iff_eq_mul]))
        (add norm 0 (by grind only [mul_two]))
        (add norm 1 (by rw [div_div]))
        (add norm 0 (by grind only [mul_div_cancel_left]))
        (add norm 0 (by grind only [sub_eq_add]))
        (add norm 1 (by rw [mul_div_cancel_right]))
        (add norm 1 (by rw [Quaternion.star_add_self]))
        (add norm 0 (by grind only [Quaternion.self_add_star]))
        (add norm 0 (by grind only [mul_div_cancel]))
        (add norm 0 (by grind only [eq_div_iff_mul_eq']))
        (add norm 0 (by grind only [Pell.d]))
        (add norm 1 (by rw [← eq_div_iff_mul_eq]))
        (add norm 0 (by grind only [Pell.isPell_norm]))
        (add norm 0 (by grind only [add_halves]))
        (add norm 0 (by grind only [Int.natCast_add]))
        (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
        (add safe 0 (by norm_num [mul_add_mul] at *))
        (add safe 1 (by rw [mul_div_assoc]))
        (add safe 100 (by rw [two_ne_zero'] at *))
        (add safe 0 (by push_cast [eq_div_iff] at *))
        (add safe 1 (by rw [div_eq_iff]))
        (add safe 1 (by rw [mul_div_cancel_left₀]))
        (add safe 0 (by simp_all [two_ne_zero]))
        (add unsafe 50% (by simp_rw [Int.emod_def]))

    let g := fun x ↦ f x - c
    have h_step18 : ∀ a b, g (a + b) = g a + g b := by
      clear * - h_step15
      aesop (config := {
        maxRuleApplications := 400
        maxRuleApplicationDepth := 10
        maxNormIterations := 30
        maxGoals := 128
        }) (rule_sets := [-builtin])
        (add norm 100 (by ring))
        (add norm 100 (by field_simp))
        (add norm 100 (by norm_num))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 100 (by abel))
        (add norm 100 (by zify))
        (add norm 100 (by bound))
        (add norm 100 (by interval_cases))
        (add norm 100 (by ext))
        (add norm 100 (by exfalso))
        (add norm 0 (by simp))
        (add norm 100 (by ring_nf at *))
        (add norm 100 (by norm_num [*] at *))
        (add norm 100 (by norm_cast at *))
        (add norm 100 (by rfl))
        (add norm 0 (by decide))
        (add norm 100 (by push_cast))
        (add norm 100 (by assumption_mod_cast))
        (add safe 1 (by ring_nf))
        (add safe 0 (by split))
        (add safe 0 (by simp_all))
        (add safe 0 (by field_simp [*] at *))
        (add norm 100 (by rw [forall_const] at *))
        (add norm 0 (by grind only [Int.natCast_add]))
        (add norm 0 (by rw [← Int.sub_eq_add_neg]))
        (add norm 0 (by grind only [Int.emod_add_ediv]))
        (add norm 100 (by rw [forall_true_iff] at *))
        (add norm 100 (by solve_by_elim [Int.neg_add]))
        (add norm 1 (by rw [mul_div_cancel_right]))
        (add norm 0 (by rw [← Int.modEq_zero_iff]))
        (add norm 0 (by grind only [mul_div_cancel]))
        (add norm 1 (by rw [AddConstMapClass.map_sub_zsmul]))
        (add norm 0 (by grind only [mul_div_cancel_left]))
        (add norm 0 (by grind only [sub_eq_add]))
        (add norm 0 (by grind only [Int.ofNat_add]))
        (add norm 100 (by rw [implies_true] at *))
        (add norm 0 (by grind only [Zsqrtd.intCast_val]))
        (add norm 0 (by rw [← SubgroupClass.coe_div]))
        (add norm 0 (by grind only [Int.ofNat_succ]))
        (add norm 100 (by rw [imp_true_iff] at *))
        (add safe 1 (by simp only [AddConstMapClass.map_add_zsmul] at *))
        (add safe 1 (by simp only [AddConstMapClass.map_zsmul_add] at *))
        (add safe 1 (by rw [Int.add_assoc]))
        (add safe 1 (by rw [Int.add_sub_cancel]))
        (add safe 1 (by simp only [div_mul] at *))
        (add unsafe 90% (by apply zpow_add))
        (add unsafe 90% (by push_cast [div_eq_mul_inv] at *))
        (add unsafe 90% (by simp_rw [zpow_sub]))
        (add unsafe 90% (by push_cast [div_inv_eq_mul] at *))
        (add unsafe 90% (by apply Int.induction_on))
        (add unsafe 90% (by simp_rw [zpow_add₀]))
        (add unsafe 90% (by apply zpow_one))
        (add unsafe 90% (by apply zpow_add_one))
        (add unsafe 90% (by simp_rw [Matrix.zpow_add_of_nonneg]))

    have h_step19 : ∃ k : ℤ, ∀ x, g x = k * x := by
      clear * - h_step18
      let k := g 1
      use k
      intro z
      induction z
      · simp [mul_zero]
        specialize h_step18 0 0 <;> simp_all
      · simp_all [add_mul, mul_add, h_step18] <;> nlinarith
      · simp_all [sub_eq_add_neg, h_step18]
        linarith [show (g (-1) : ℤ) = -k by have h := h_step18 (-1) 1; simp [sub_eq_add_neg] at h; linarith]

    obtain ⟨k, hk⟩ := h_step19
    have h_step20 : ∀ x, f x = k * x + c := by
      clear * - hk
      aesop (config := {
        maxRuleApplicationDepth := 10
        maxNormIterations := 30
        maxGoals := 256
        }) (rule_sets := [-builtin])
        (add norm 100 (by ring))
        (add norm 100 (by field_simp))
        (add norm 100 (by norm_num))
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 100 (by abel))
        (add norm 100 (by zify))
        (add norm 0 (by gcongr))
        (add norm 100 (by bound))
        (add norm 0 (by interval_cases))
        (add norm 0 (by ext))
        (add norm 100 (by exfalso))
        (add norm 0 (by simp))
        (add norm 0 (by ring_nf at *))
        (add norm 100 (by field_simp [*] at *))
        (add norm 100 (by norm_num [*] at *))
        (add norm 100 (by norm_cast at *))
        (add norm 100 (by rfl))
        (add norm 0 (by decide))
        (add norm 100 (by push_cast))
        (add norm 100 (by assumption_mod_cast))
        (add safe 1 (by ring_nf))
        (add safe 0 (by split))
        (add unsafe 90% (by simp_all))
        (add norm 100 (by rw [div_eq_one] at *))
        (add norm 100 (by rw [div_self'] at *))
        (add norm 1 (by simp_all [div_eq_iff_eq_mul]))
        (add norm 0 (by rw [← AddConstMapClass.map_sub_const]))
        (add norm 1 (by simp_all [AddConstMapClass.map_sub_zsmul]))
        (add norm 1 (by simp_all [LinearPMap.map_sub]))
        (add norm 100 (by rw [LinearMap.BilinForm.sub_left] at *))
        (add norm 1 (by simp_all [Int.modEq_iff_dvd]))
        (add norm 0 (by rw [← ContinuousAlternatingMap.sub_apply]))
        (add norm 1 (by simp_all [AddCommGroup.ModEq]))
        (add norm 1 (by rw [mul_div_cancel_left]))
        (add norm 1 (by rw [mul_div_cancel]))
        (add norm 1 (by simp_all [WeakFEPair.functional_equation]))
        (add norm 1 (by simp_all [div_eq_iff_eq_mul']))
        (add norm 0 (by rw [← CompactlySupportedContinuousMap.sub_apply]))
        (add norm 100 (by rw [LinearMap.map_sub] at *))
        (add norm 1 (by simp_all [eq_div_iff_mul_eq']))
        (add norm 0 (by rw [← SubgroupClass.coe_div]))
        (add norm 0 (by rw [← LinearMap.BilinForm.sub_right]))
        (add norm 0 (by rw [← AddConstMapClass.map_sub_int']))
        (add norm 1 (by simp_all [ContinuousMultilinearMap.sub_apply]))
        (add norm 0 (by rw [← Real.Angle.coe_sub]))
        (add norm 0 (by rw [← groupCohomology.dZero]))
        (add norm 1 (by rw [mul_div_cancel_right]))
        (add norm 0 (by rw [← sub_lie]))
        (add norm 0 (by rw [← Int.modEq_zero_iff]))
        (add norm 1 (by simp_all [AddConstMapClass.map_sub_nsmul]))
        (add norm 1 (by simp_all [eq_comm]))
        (add norm 0 (by rw [← Matrix.charmatrix_apply_eq]))
        (add norm 0 (by rw [← SchwartzMap.sub_apply]))
        (add unsafe 90% (by push_cast [div_eq_mul_inv] at *))
        (add unsafe 90% (by push_cast [div_inv_eq_mul] at *))

    have h_step25 : 2 * k - k ^ 2 = 0 := by
      clear * - h_eq h_step20
      have h1 := h_eq 0 0
      have h2 := h_eq 1 0
      simp_all [h_step20, mul_add]
      nlinarith [sq_nonneg (k - 2), sq_nonneg (k + 1)]

    have h_step26 : 2 * c - k * c = 0 := by
      clear * - h_eq h_step20
      have h₁ := h_eq 0 (0)
      ring_nf at h₁ <;> simp_all
      nlinarith [h_eq 1 0, h_eq 0 1, h_eq 1 1, h_eq (-1) 1]

    have h_step27 : k = 0 ∨ k = 2 := by
      clear * - h_step25
      classical
      have : k ≤ 2 := by nlinarith
      have : k ≥ 0 := by nlinarith
      interval_cases k <;> simp_all

    cases h_step27 with
    | inl h_k0 =>
      have h_c0 : c = 0 := by
        clear * - h_step26 h_k0
        aesop (config := {
          maxRuleApplications := 100
          maxRuleApplicationDepth := 10
          maxNormIterations := 60
          maxGoals := 32
          enableUnfold := false
          })
          (add norm 100 (by ring))
          (add norm 100 (by field_simp))
          (add norm 100 (by norm_num))
          (add norm 100 (by norm_cast))
          (add norm 0 (by linarith))
          (add norm 0 (by nlinarith))
          (add norm 0 (by omega))
          (add norm 100 (by abel))
          (add norm 100 (by zify))
          (add norm 0 (by gcongr))
          (add norm 0 (by bound))
          (add norm 100 (by interval_cases))
          (add norm 100 (by ext))
          (add norm 100 (by exfalso))
          (add norm 0 (by simp))
          (add norm 100 (by ring_nf at *))
          (add norm 1 (by field_simp [*] at *))
          (add norm 100 (by norm_num [*] at *))
          (add norm 100 (by norm_cast at *))
          (add norm 100 (by rfl))
          (add norm 100 (by push_cast))
          (add norm 100 (by assumption_mod_cast))
          (add safe 0 (by ring_nf))
          (add safe 0 (by split))
          (add unsafe 90% (by simp_all))
          (add norm 0 (by grind only [Zsqrtd.norm_eq_zero]))
          (add norm 0 (by grind only [MulZeroClass]))
          (add norm 0 (by grind only [zero_div]))
          (add norm 0 (by grind only [div_zero]))
          (add norm 0 (by simp [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero'] at *))
          (add norm 0 (by grind only [Zsqrtd.norm_eq_zero_iff]))
          (add norm 0 (by apply Zsqrtd.intCast_im))
          (add norm 0 (by simp [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero] at *))
          (add safe 1 (by rw [← Zsqrtd.norm_zero] at *))
          (add safe 0 (by field_simp [legendreSym.eq_zero_iff] at *))
          (add unsafe 50% (by simp_rw [Zsqrtd.zero_re]))
          (add unsafe 50% (by simp_rw [Zsqrtd.zero_im]))
          (add unsafe 50% (by simp_rw [Int.cast_zero]))
          (add unsafe 50% (by simp_rw [zero_pow]))
          (add unsafe 50% (by simp_rw [Quaternion.coe_zero]))
          (add unsafe 50% (by simp_rw [Int.cast_eq_zero]))
          (add unsafe 50% (by simp_rw [Int.natCast_eq_zero]))
          (add unsafe 50% (by simp_rw [quadraticChar_zero]))
          (add unsafe 50% (by simp_rw [GaussianInt.toComplex_zero]))
          (add unsafe 50% (by simp_rw [ZNum.cast_zero]))
          (add unsafe 50% (by simp_rw [GaussianInt.toComplex_eq_zero]))
          (add unsafe 50% (by simp_rw [jacobiTheta₂_undef]))
          (add unsafe 50% (by simp_rw [Quaternion.zero_re]))
          (add unsafe 50% (by simp_rw [Int.ofNat_zero]))
          (add unsafe 50% (by simp_rw [jacobiTheta₂'_undef]))
          (add unsafe 50% (by simp_rw [pow_eq_zero]))
          (add unsafe 50% (by simp_rw [MulChar.map_zero]))
          (add unsafe 50% (by simp_rw [Quaternion.normSq_eq_zero]))
          (add unsafe 50% (by simp_rw [Int.natAbs_zero]))
          (add unsafe 50% (by simp_rw [Complex.zero_cpow]))
          (add unsafe 50% (by simp_rw [Complex.ofReal_zero]))
          (add unsafe 50% (by simp_rw [mul_eq_zero]))

      have h_sol_1 : ∀ z, f z = 0 := by
        clear * - h_step20 h_c0 h_k0
        aesop (config := {
          maxRuleApplicationDepth := 220
          maxNormIterations := 60
          maxGoals := 32
          enableUnfold := false
          }) (rule_sets := [-builtin])
          (add norm 100 (by ring))
          (add norm 100 (by field_simp))
          (add norm 100 (by norm_num))
          (add norm 100 (by norm_cast))
          (add norm 0 (by linarith))
          (add norm 0 (by nlinarith))
          (add norm 0 (by omega))
          (add norm 100 (by abel))
          (add norm 100 (by zify))
          (add norm 0 (by gcongr))
          (add norm 0 (by bound))
          (add norm 100 (by interval_cases))
          (add norm 0 (by ext))
          (add norm 100 (by exfalso))
          (add norm 0 (by simp))
          (add norm 100 (by ring_nf at *))
          (add norm 100 (by norm_num [*] at *))
          (add norm 100 (by norm_cast at *))
          (add norm 100 (by rfl))
          (add norm 100 (by push_cast))
          (add norm 100 (by assumption_mod_cast))
          (add safe 0 (by ring_nf))
          (add safe 0 (by split))
          (add safe 1 (by field_simp [*] at *))
          (add unsafe 90% (by simp_all))
          (add norm 0 (by grind only [MulZeroClass]))
          (add norm 0 (by grind only [div_zero]))
          (add norm 0 (by grind only [zero_div]))
          (add norm 0 (by grind only [Zsqrtd.norm_eq_zero]))
          (add norm 0 (by grind only [TrivSqZeroExt.inl_zero]))
          (add safe 1 (by simp_all [Zsqrtd.zero_re]))
          (add safe 1 (by rw [← Zsqrtd.zero_im] at *))
          (add safe 1 (by rw [← Zsqrtd.norm_zero] at *))
          (add safe 1 (by rw [MulChar.map_zero]))
          (add safe 0 (by field_simp [Int.natAbs_zero] at *))
          (add safe 1 (by rw [← Zsqrtd.intCast_im] at *))
          (add unsafe 50% (by simp_rw [Int.cast_zero]))
          (add unsafe 10% (by solve_by_elim [zero_pow]))
          (add unsafe 50% (by simp_rw [Quaternion.coe_zero]))
          (add unsafe 50% (by simp_rw [Int.ofNat_zero]))
          (add unsafe 50% (by simp_rw [ZNum.cast_zero]))
          (add unsafe 50% (by simp_rw [quadraticChar_zero]))
          (add unsafe 50% (by simp_rw [Nat.cast_zero]))
          (add unsafe 50% (by simp_rw [EReal.coe_zero]))
          (add unsafe 50% (by simp_rw [Complex.zero_cpow]))
          (add unsafe 50% (by simp_rw [Complex.ofReal_zero]))
          (add unsafe 50% (by simp_rw [Int.natCast_eq_zero]))
          (add unsafe 50% (by simp_rw [Quaternion.zero_re]))
          (add unsafe 50% (by simp_rw [Int.natCast_zero]))
          (add unsafe 50% (by simp_rw [Complex.logTaylor_at_zero]))
          (add unsafe 50% (by simp_rw [jacobiTheta₂'_undef]))
          (add unsafe 50% (by simp_rw [FiniteField.cast_card_eq_zero]))
          (add unsafe 50% (by simp_rw [Int.sign_zero]))
          (add unsafe 50% (by simp_rw [Hyperreal.coe_zero]))
          (add unsafe 50% (by simp_rw [GaussianInt.toComplex_zero]))
          (add unsafe 50% (by simp_rw [jacobiTheta₂_undef]))
          (add unsafe 50% (by simp_rw [eq_self_iff_true]))

      exact λ z => Or.inl (h_sol_1 z)

    | inr h_k2 =>
      have h_sol_2 : ∃ c', ∀ z, f z = 2 * z + c' := by
        clear * - h_step20 h_k2
        simp [h_k2, h_step20]

      obtain ⟨c'', hc''⟩ := h_sol_2
      exact fun z => Or.inr ⟨c'', hc''⟩

  · -- Reverse direction
    intro h_sol
    aesop (config := {
      maxRuleApplications := 400
      maxRuleApplicationDepth := 120
      maxNormIterations := 800
      maxGoals := 128
      })
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 100 (by nlinarith))
      (add norm 100 (by abel))
      (add norm 100 (by push_neg))
      (add norm 100 (by zify))
      (add norm 100 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by decide))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by omega))
      (add safe 0 (by simp_all))
      (add safe 0 (by rfl))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [Nat.cast_two]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Ring.multichoose_two]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 1 (by norm_num [CharTwo.two_eq_zero] at *))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
      (add norm 1 (by norm_num [Nat.cast_descFactorial_two] at *))
      (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
      (add norm 0 (by grind only [Nat.fib_two_mul]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self']))
      (add unsafe 50% (by simp only [Int.cast_two]))
      (add unsafe 50% (by simp only [zpow_two]))
      (add unsafe 10% (by simp_all [Real.sin_two_mul]))
      (add unsafe 90% (by grind only [Nat.factorial_two]))
      (add unsafe 90% (by grind only [Complex.cpow_two]))
      (add unsafe 90% (by grind only [Complex.sin_two_mul]))
      (add unsafe 90% (by grind only [Real.two_mul_arctan_add_pi]))
