import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  have h1 : (a / sqrt b - sqrt b) ^ 2 ≥ 0 := by
    clear * - h₀
    first
    | positivity
    | apply sq_nonneg

  have h2 : a ^ 2 / b - 2 * a + b ≥ 0 := by
    clear * - h1 h₀
    have S := h₀.1
    have b_pos := h₀.2.1
    field_simp [sq, b_pos.ne'] at h1
    field_simp at * <;> nlinarith [Real.sq_sqrt b_pos.le, sq_nonneg (a - b)]

  have h3 : a ^ 2 / b + b ≥ 2 * a := by
    clear * - h2
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 60
      maxGoals := 128
      })
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 100 (by nlinarith))
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
      (add norm 100 (by decide))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by omega))
      (add safe 0 (by simp_all))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 100 (by rw [one_le_two] at *))
      (add norm 100 (by rw [Real.pi_le_four]))
      (add norm 100 (by rw [le_div_iff']))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 100 (by simp only [mul_comm] at *))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 100 (by positivity [zero_le_two]))
      (add norm 0 (by grind only [mul_lt_mul_left]))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [sub_half]))
      (add norm 100 (by rw [Real.two_le_pi] at *))
      (add norm 100 (by simp only [mul_right_comm] at *))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 100 (by rw [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [le_of_mul_le_mul_left]))
      (add safe 0 (by rw [mul_le_mul_left] at *))
      (add safe 0 (by rw [mul_le_mul_right] at *))
      (add safe 1 (by rw [mul_le_mul_of_nonneg_left]))
      (add safe 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by apply le_div_iff))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le]))
      (add unsafe 50% (by apply div_le_iff))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul]))
      (add unsafe 50% (by apply div_le_iff'))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le']))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul']))

  have h4 : (b / sqrt c - sqrt c) ^ 2 ≥ 0 := by
    clear * - h₀
    apply pow_two_nonneg

  have h5 : b ^ 2 / c - 2 * b + c ≥ 0 := by
    clear * - h4 h₀
    rcases h₀ with ⟨_, _, _, _⟩
    field_simp [sq, mul_add] at h4
    field_simp [sq] at *
    repeat' nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ c)]

  have h6 : b ^ 2 / c + c ≥ 2 * b := by
    clear * - h5
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 60
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
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by simp_all))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 100 (by simp only [mul_right_comm] at *))
      (add norm 0 (by grind only [mul_div_assoc]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_div]))
      (add norm 100 (by simp only [mul_comm] at *))
      (add norm 0 (by grind only [div_div]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [div_mul]))
      (add norm 100 (by simp only [mul_assoc] at *))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 100 (by rw [le_div_iff']))
      (add norm 100 (by rw [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 100 (by rw [one_le_two] at *))
      (add norm 100 (by simp only [mul_left_comm] at *))
      (add norm 100 (by rw [Real.pi_le_four]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add safe 1 (by rw [mul_le_mul_left]))
      (add safe 1 (by rw [mul_le_mul_right]))
      (add safe 1 (by rw [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by apply le_div_iff))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le]))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul]))
      (add unsafe 50% (by apply div_le_iff))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul']))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le']))
      (add unsafe 50% (by apply div_le_iff'))

  have h7 : (c / sqrt d - sqrt d) ^ 2 ≥ 0 := by
    clear * - h₀
    apply sq_nonneg

  have h8 : c ^ 2 / d - 2 * c + d ≥ 0 := by
    clear * - h7 h₀
    apply le_of_sub_nonneg
    rcases h₀ with ⟨_, _, _, _⟩
    field_simp [sq, mul_add] at *
    nlinarith [Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ d)]

  have h9 : c ^ 2 / d + d ≥ 2 * c := by
    clear * - h8
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 60
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
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by simp_all))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 100 (by simp only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 100 (by rw [div_le_iff]))
      (add norm 100 (by simp only [mul_comm] at *))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 100 (by rw [div_le_iff']))
      (add norm 100 (by simp only [mul_right_comm] at *))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 0 (by grind only [sub_half]))
      (add norm 0 (by grind only [half_add_self]))
      (add norm 0 (by grind only [add_halves']))
      (add norm 0 (by grind only [mul_div_assoc]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [add_self_div_two]))
      (add norm 0 (by grind only [mul_div]))
      (add safe 1 (by rw [mul_le_mul_left]))
      (add safe 1 (by linarith [one_le_two]))
      (add safe 1 (by rw [mul_le_mul_right]))
      (add safe 100 (by rw [two_ne_zero'] at *))
      (add safe 0 (by simp_all [two_ne_zero]))
      (add safe 1 (by linarith [zero_le_two]))
      (add unsafe 50% (by apply le_div_iff))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul]))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le]))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul']))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le']))

  have h10 : (d / sqrt a - sqrt a) ^ 2 ≥ 0 := by
    clear * - h₀
    first
    | positivity
    | apply sq_nonneg

  have h11 : d ^ 2 / a - 2 * d + a ≥ 0 := by
    clear * - h10 h₀
    obtain ⟨a_pos, b_pos, c_pos, d_pos⟩ := h₀
    field_simp [sq, a_pos.ne'] at h10 ⊢
    nlinarith [Real.mul_self_sqrt a_pos.le, sq_nonneg (d - √a), d_pos]

  have h12 : d ^ 2 / a + a ≥ 2 * d := by
    clear * - h11
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
      (add norm 100 (by decide))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by simp_all))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 100 (by rw [one_le_two] at *))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 100 (by simp only [mul_comm] at *))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [zero_lt_two']))
      (add norm 100 (by simp only [mul_assoc] at *))
      (add norm 100 (by simp only [mul_right_comm] at *))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 100 (by rw [div_le_iff]))
      (add norm 100 (by simp only [mul_left_comm] at *))
      (add norm 100 (by positivity [zero_le_two]))
      (add norm 100 (by rw [div_le_iff']))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [zero_lt_two]))
      (add norm 100 (by rw [Real.pi_le_four]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [ack_two]))
      (add safe 0 (by rw [mul_le_mul_left] at *))
      (add safe 1 (by rw [mul_le_mul_of_nonneg_left]))
      (add safe 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add safe 1 (by rw [mul_le_mul]))
      (add safe 0 (by simp_all [two_ne_zero]))
      (add unsafe 50% (by apply le_div_iff))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le]))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul]))
      (add unsafe 10% (by rw [mul_le_mul_right]))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul']))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le']))

  have h13 : (a ^ 2 / b + b) + (b ^ 2 / c + c) + (c ^ 2 / d + d) + (d ^ 2 / a + a) ≥ 2 * a + 2 * b + 2 * c + 2 * d := by
    clear * - h3 h6 h9 h12
    aesop (config := {
      maxRuleApplicationDepth := 220
      maxNormIterations := 520
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
      (add norm 0 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by ring_nf))
      (add safe 0 (by simp_all))
      (add norm 100 (by simp only [mul_le_mul_right']))
      (add norm 100 (by simp only [mul_le_mul_left']))
      (add norm 100 (by simp only [mul_le_mul_iff_left]))
      (add norm 100 (by simp only [mul_le_mul']))
      (add norm 100 (by simp only [mul_right_comm] at *))
      (add norm 100 (by simp only [mul_left_comm] at *))
      (add norm 100 (by norm_num [mul_le_mul] at *))
      (add norm 100 (by simp only [mul_assoc] at *))
      (add norm 100 (by simp only [mul_comm] at *))
      (add norm 100 (by simp only [mul_le_mul_iff_right]))
      (add norm 100 (by norm_num [mul_add_mul_le_mul_add_mul] at *))
      (add norm 0 (by grind only [le_trans]))
      (add norm 100 (by rw [le_div_iff]))
      (add norm 0 (by grind only [le_mul_tsub]))
      (add norm 0 (by grind only [le_mul_left]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 100 (by rw [one_add_mul_le_pow]))
      (add norm 0 (by grind only [Real.BohrMollerup.f_add_nat_ge]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Finset.mul_pluennecke_petridis]))
      (add safe 1 (by push_cast [mul_le_mul_left] at *))
      (add safe 1 (by rw [mul_le_mul_of_nonneg_left]))
      (add safe 1 (by rw [mul_le_mul_of_nonneg_right]))
      (add safe 1 (by linarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add safe 1 (by push_cast [mul_le_mul_right] at *))
      (add safe 0 (by grind only [Ordnode.Valid'.node4L_lemma₅]))
      (add safe 0 (by norm_num [mul_add_mul] at *))
      (add safe 1 (by linarith [one_le_two]))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul]))
      (add unsafe 50% (by simp_rw [le_div_iff_mul_le]))
      (add unsafe 90% (by rw [SzemerediRegularity.m_add_one_div_m_le_one_add] at *))
      (add unsafe 50% (by simp_rw [div_le_iff_le_mul']))

  have h14 : (a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a) + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    clear * - h13
    aesop (config := {
      maxRuleApplicationDepth := 220
      maxNormIterations := 320
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
      (add norm 0 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by ring_nf))
      (add safe 0 (by simp_all))
      (add norm 100 (by simp_all only [mul_le_mul_right']))
      (add norm 100 (by simp_all only [mul_le_mul_left']))
      (add norm 100 (by simp_all only [mul_le_mul']))
      (add norm 100 (by simp only [mul_le_mul_iff_left]))
      (add norm 100 (by simp only [mul_le_mul_iff_right]))
      (add norm 100 (by simp only [mul_right_comm] at *))
      (add norm 100 (by norm_num [mul_add_mul_le_mul_add_mul] at *))
      (add norm 100 (by simp only [mul_left_comm] at *))
      (add norm 0 (by grind only [le_trans]))
      (add norm 100 (by simp only [mul_assoc] at *))
      (add norm 100 (by simp only [mul_comm] at *))
      (add norm 100 (by rw [one_add_mul_le_pow]))
      (add norm 100 (by rw [le_div_iff]))
      (add safe 1 (by rw [mul_le_mul_of_nonneg_left]))
      (add safe 1 (by rw [mul_le_mul]))
      (add safe 1 (by push_cast [mul_le_mul_left] at *))
      (add safe 1 (by rw [mul_le_mul_of_nonneg_right]))
      (add safe 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add safe 1 (by push_cast [mul_le_mul_right] at *))
      (add safe 0 (by grind only [Ordnode.Valid'.node4L_lemma₅]))
      (add safe 1 (by linarith [one_le_two]))
      (add safe 0 (by grind only [Ordnode.Valid'.node4L_lemma₁]))
      (add safe 1 (by rw [le_mul_of_one_le_left]))
      (add safe 1 (by rw [mul_self_le_mul_self]))
      (add safe 0 (by nlinarith [le_mul_of_one_le_right']))
      (add safe 0 (by simp_all [mul_lt_mul]))
      (add safe 0 (by grind only [Ordnode.ratio]))
      (add safe 0 (by grind only [Ordnode.Valid'.rotateL_lemma₂]))
      (add safe 0 (by grind only [Ordnode.Valid'.rotateL_lemma₁]))
      (add safe 0 (by grind only [Ordnode.Valid'.node4L_lemma₄]))
      (add safe 0 (by grind only [Ordnode.Valid'.merge_lemma]))
      (add unsafe 10% (by nlinarith [pow_le_pow_left]))

  have h15 : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    clear * - h14
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
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
      (add norm 0 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 0 (by simp_all))
      (add norm 100 (by simp only [mul_le_mul_iff_left]))
      (add norm 100 (by simp only [mul_le_mul_right']))
      (add norm 100 (by simp only [mul_le_mul_left']))
      (add norm 100 (by simp only [mul_le_mul']))
      (add norm 100 (by simp only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 100 (by simp only [mul_right_comm] at *))
      (add norm 0 (by grind only [mul_two]))
      (add norm 100 (by simp only [mul_left_comm] at *))
      (add norm 100 (by simp only [mul_comm] at *))
      (add norm 100 (by norm_num [mul_add_mul_le_mul_add_mul] at *))
      (add norm 100 (by simp only [mul_assoc] at *))
      (add norm 100 (by positivity [le_mul_of_one_le_right']))
      (add norm 100 (by rw [le_div_iff]))
      (add norm 100 (by positivity [le_mul_of_one_le_left']))
      (add norm 0 (by grind only [Real.BohrMollerup.f_add_nat_ge]))
      (add norm 100 (by rw [one_add_mul_le_pow]))
      (add norm 0 (by grind only [le_mul_left]))
      (add norm 0 (by grind only [zero_lt_two']))
      (add safe 1 (by push_cast [mul_le_mul_left] at *))
      (add safe 1 (by rw [mul_le_mul_of_nonneg_left]))
      (add safe 1 (by rw [mul_le_mul]))
      (add safe 1 (by linarith [one_le_two]))
      (add safe 1 (by linarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add safe 1 (by rw [mul_le_mul_of_nonneg_right]))
      (add safe 1 (by push_cast [mul_le_mul_right] at *))
      (add safe 1 (by linarith [two_mul_le_add_sq]))
      (add safe 1 (by linarith [zero_le_two]))
      (add safe 1 (by rw [le_mul_of_one_le_left]))
      (add safe 0 (by grind only [Ordnode.ratio]))
      (add safe 1 (by simp only [le_mul_of_one_le_right] at *))
      (add safe 0 (by grind only [Ordnode.Valid'.node4L_lemma₅]))

  exact h15
