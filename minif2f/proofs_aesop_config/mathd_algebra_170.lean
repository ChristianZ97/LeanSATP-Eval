import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
  S.card = 11 := by
  have h_rhs : (5 : ℚ) + (6 : ℚ) / 10 = (56 : ℚ) / 10 := by
    clear * -
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 30
      maxGoals := 128
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
      (add norm 100 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 0 (by decide))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by ring_nf))
      (add safe 0 (by simp_all))
      (add norm 100 (by apply div_self))
      (add norm 100 (by apply sub_div))
      (add norm 1 (by linarith [add_div]))
      (add norm 100 (by apply mul_one_div))
      (add norm 0 (by grind only [mul_div]))
      (add norm 0 (by grind only [mul_div_assoc]))
      (add norm 0 (by grind only [div_right_comm]))
      (add norm 100 (by apply div_mul_cancel₀))
      (add norm 100 (by apply mul_div_cancel₀))
      (add norm 0 (by grind only [div_mul]))
      (add norm 100 (by apply mul_div_mul_left))
      (add norm 100 (by apply div_eq_one_iff_eq))
      (add norm 0 (by grind only [Real.div_sqrt]))
      (add norm 0 (by grind only [eq_div_iff]))
      (add norm 0 (by grind only [tsub_div]))
      (add norm 0 (by grind only [div_sub']))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 1 (by linarith [Real.log_div]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [mul_div_right_comm]))
      (add norm 0 (by grind only [div_eq_iff]))
      (add norm 0 (by grind only [goldenConj]))
      (add norm 0 (by grind only [CircleDeg1Lift.transnumAuxSeq]))
      (add norm 0 (by grind only [div_add_div_same]))
      (add safe 0 (by simp_all [div_div]))
      (add safe 0 (by simp_all [mul_div_cancel_left₀]))
      (add safe 0 (by simp_all [two_ne_zero']))
      (add safe 0 (by simp_all [mul_div_cancel_right₀]))
      (add safe 0 (by simp_all [Real.cos_sq]))
      (add safe 0 (by simp_all [Real.sin_sq_eq_half_sub]))
      (add safe 0 (by simp_all [Real.Gamma_two]))
      (add safe 0 (by simp_all [two_ne_zero]))

  have h_unpack : ∀ n : ℤ, abs (n - 2) ≤ (56 : ℚ) / 10 ↔ -(56 : ℚ) / 10 ≤ (n - 2 : ℚ) ∧ (n - 2 : ℚ) ≤ (56 : ℚ) / 10 := by
    intro n
    clear * -
    field_simp [abs_le]
    norm_cast <;> norm_num
    cases abs_cases (n - 2) <;> (try simp [*]) <;> omega

  have h_shift : ∀ n : ℤ, -(56 : ℚ) / 10 ≤ (n - 2 : ℚ) ∧ (n - 2 : ℚ) ≤ (56 : ℚ) / 10 ↔ (-36 : ℚ) / 10 ≤ (n : ℚ) ∧ (n : ℚ) ≤ (76 : ℚ) / 10 := by
    intro n
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 30
      maxGoals := 1024
      })
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 100 (by nlinarith))
      (add norm 100 (by abel))
      (add norm 0 (by push_neg))
      (add norm 100 (by zify))
      (add norm 100 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 0 (by ring_nf))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 100 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 0 (by decide))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by omega))
      (add safe 0 (by simp_all))
      (add norm 100 (by rw [div_le_div_iff_left]))
      (add norm 100 (by rw [div_le_div_right]))
      (add norm 100 (by rw [div_le_iff']))
      (add norm 100 (by rw [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 100 (by rw [div_le_one]))
      (add norm 100 (by rw [div_le_div_iff]))
      (add norm 100 (by rw [le_div_iff']))
      (add norm 100 (by rw [div_le_div_left]))
      (add norm 100 (by rw [Real.pi_le_four]))
      (add norm 100 (by rw [Real.pi_div_two_le_two]))
      (add safe 1 (by grind only [Int.le_floor]))
      (add safe 1 (by grind only [Int.floor_le]))
      (add safe 1 (by grind only [Int.cast_le]))
      (add safe 1 (by grind only [Int.lt_iff_add_one_le]))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le]))
      (add unsafe 50% (by apply le_div_iff))
      (add unsafe 50% (by apply div_le_iff))
      (add unsafe 50% (by simp_rw [Real.logb_le_logb]))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le']))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul]))
      (add unsafe 50% (by simp_rw [inv_le_inv_iff]))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul']))
      (add unsafe 50% (by simp_rw [inv_le]))
      (add unsafe 50% (by simp_rw [smul_le_smul_iff_of_pos_left]))
      (add unsafe 10% (by rw [inv_div]))
      (add unsafe 50% (by simp_rw [Real.logb_le_logb_of_base_lt_one]))
      (add unsafe 10% (by rw [CircleDeg1Lift.le_translationNumber_of_add_int_le]))
      (add unsafe 50% (by simp_rw [Real.logb_le_iff_le_rpow]))
      (add unsafe 10% (by rw [neg_div]))
      (add unsafe 10% (by rw [abs_le]))
      (add unsafe 50% (by simp_rw [le_inv]))
      (add unsafe 50% (by simp_rw [inv_le']))

  have h_int_range : ∀ n : ℤ, (-36 : ℚ) / 10 ≤ (n : ℚ) ∧ (n : ℚ) ≤ (76 : ℚ) / 10 ↔ -3 ≤ n ∧ n ≤ 7 := by
    intro n
    clear * -
    norm_num (config := { decide := true })
    field_simp <;> norm_cast at * <;> omega

  have h_S_char : ∀ n : ℤ, n ∈ S ↔ -3 ≤ n ∧ n ≤ 7 := by
    intro n
    clear * - h₀ h_rhs h_unpack h_shift h_int_range
    simp_all [-le_abs]
    norm_num [abs_le] <;> omega

  have h_S : S = Finset.Icc (-3 : ℤ) 7
  · ext a <;> simp [h_S_char]
  · all_goals simp [h_S]
