
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

theorem amc12_2001_p21 (a b c d : ℕ) (h₀ : a * b * c * d = 8!) (h₁ : a * b + a + b = 524)
    (h₂ : b * c + b + c = 146) (h₃ : c * d + c + d = 104) : ↑a - ↑d = (10 : ℤ) := by
  -- Step 1 & 2 & 3: Transform h1 into (a+1)(b+1) = 525
  have h₁' : (a + 1) * (b + 1) = 525 := by
    clear * - h₁
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.mul_succ]))
      (add norm 0 (by grind only [Nat.mul_add]))
      (add norm 0 (by grind only [Nat.add_comm]))
      (add norm 0 (by grind only [Nat.add_mul]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [Nat.add_assoc]))
      (add norm 0 (by grind only [Nat.add_succ]))
      (add norm 0 (by grind only [Nat.succ_add]))
      (add norm 0 (by grind only [Nat.add_right_comm]))
      (add norm 0 (by grind only [Nat.one_mul]))
      (add norm 0 (by grind only [Nat.pow_add]))
      (add norm 0 (by grind only [Num.add_succ]))
      (add norm 0 (by grind only [Nat.add_right_cancel]))
      (add norm 0 (by grind only [Nat.add_left_comm]))
      (add norm 0 (by grind only [add_idem]))
      (add norm 0 (by grind only [Nat.left_distrib]))
      (add norm 0 (by grind only [Nat.succ_add_eq_add_succ]))
      (add norm 0 (by grind only [Nat.mul_one]))
      (add norm 0 (by grind only [Num.add_of_nat]))
      (add norm 0 (by grind only [Zsqrtd.SqLe]))
      (add norm 0 (by grind only [Num.cast_add]))
      (add norm 0 (by grind only [Nat.mul_comm]))
      (add norm 0 (by grind only [Nat.one_add]))
      (add norm 0 (by grind only [Nat.succ_mul_succ]))
      (add norm 0 (by grind only [Num.add_to_nat]))
      (add norm 0 (by grind only [Nat.ascFactorial_succ]))
      (add norm 0 (by grind only [Zsqrtd.sqLe_smul]))
      (add norm 0 (by grind only [Nat.pow_succ]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Nat.succ_add_sub_one]))
      (add norm 0 (by grind only [Nat.add_zero]))
      (add norm 0 (by grind only [Nat.add_one]))

  -- Step 4 & 5 & 6: Transform h2 into (b+1)(c+1) = 147
  have h₂' : (b + 1) * (c + 1) = 147 := by
    clear * - h₂
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
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Nat.mul_succ]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [Nat.mul_one]))
      (add norm 0 (by grind only [Nat.succ_eq_add_one]))
      (add norm 0 (by grind only [Nat.succ_add_sub_one]))
      (add norm 0 (by grind only [Nat.add_succ]))
      (add norm 0 (by grind only [Nat.mul_add]))
      (add norm 0 (by grind only [Nat.succ_add]))
      (add norm 0 (by grind only [Nat.factorial_succ]))
      (add norm 0 (by grind only [Nat.one_add]))
      (add norm 0 (by grind only [Nat.add_succ_sub_one]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by grind only [Nat.superFactorial_succ]))
      (add norm 0 (by grind only [Nat.add_comm]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [Nat.fib_add]))
      (add norm 0 (by grind only [Nat.add_mul]))
      (add norm 0 (by grind only [Nat.add_one]))
      (add norm 0 (by grind only [Nat.add_sub_cancel]))
      (add norm 0 (by grind only [Nat.succ_add_eq_add_succ]))
      (add norm 0 (by grind only [Nat.choose_succ_succ]))
      (add norm 0 (by grind only [Nat.left_distrib]))
      (add norm 0 (by grind only [Nat.succ_mul_succ]))
      (add norm 0 (by grind only [add_self]))
      (add norm 0 (by grind only [add_idem]))
      (add norm 0 (by grind only [Pell.xn_succ]))
      (add norm 0 (by grind only [Num.cast_succ]))

  -- Step 7 & 8 & 9: Transform h3 into (c+1)(d+1) = 105
  have h₃' : (c + 1) * (d + 1) = 105 := by
    clear * - h₃
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 512
      enableSimp := false
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.mul_succ]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [Nat.add_succ]))
      (add norm 0 (by grind only [Nat.one_add]))
      (add norm 0 (by grind only [Nat.succ_add]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Nat.add_comm]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Nat.mul_one]))
      (add norm 0 (by grind only [Nat.succ_add_sub_one]))
      (add norm 0 (by grind only [Nat.succ_eq_add_one]))
      (add norm 0 (by grind only [Nat.mul_add]))
      (add norm 0 (by grind only [add_idem]))
      (add norm 0 (by grind only [Num.add_succ]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Nat.succ_add_eq_add_succ]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [Nat.add_one]))
      (add norm 0 (by grind only [Nat.add_succ_sub_one]))
      (add norm 0 (by grind only [add_self]))
      (add norm 0 (by grind only [Nat.fib_add]))
      (add norm 0 (by grind only [Nat.add_assoc]))
      (add norm 0 (by grind only [Nat.add_mul]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Nat.add_right_comm]))
      (add norm 0 (by grind only [Nat.factorial_succ]))
      (add norm 0 (by grind only [Nat.superFactorial_succ]))
      (add norm 0 (by grind only [Nat.one_mul]))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [Num.add_one]))
      (add norm 0 (by grind only [Pell.xn_succ_succ]))

  -- Step 10, 11, 12: Establish ratio between a+1 and c+1
  -- Since we are working with naturals, we deduce divisibility properties directly.
  -- From (a+1)(b+1)=525 and (b+1)(c+1)=147, we know gcd(a+1, c+1) relates to common factors of 525 and 147 via b+1.
  -- Let's define k such that it captures the common divisor logic from the informal proof.
  -- The informal proof introduces k. Let's formalize the existence of such k based on GCDs.
  -- Note: In Lean, division / on Nat is integer division. We need to be careful.
  -- The informal proof uses rational numbers essentially.
  -- However, since (a+1), (b+1), etc are natural numbers, we can work with them directly.
  -- From h₁' and h₂':
  -- (a+1)/(c+1) = 525/147 = 25/7.
  -- This implies 7*(a+1) = 25*(c+1).
  have h_ratio_eq : 7 * (a + 1) = 25 * (c + 1) := by
    -- Proof sketch: (a+1)(b+1)=525, (b+1)(c+1)=147.
    -- Therefore (a+1)*147 = 525*(c+1) => (a+1)*147 = (c+1)*525.
    -- Divide by 21: (a+1)*7 = (c+1)*25.
    clear * - h₁' h₂'
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
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [Nat.mul_succ]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Nat.mul_add]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Nat.mul_one]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Nat.factorial_succ]))
      (add norm 0 (by grind only [Nat.superFactorial_succ]))
      (add norm 0 (by grind only [Nat.add_mul]))
      (add norm 0 (by grind only [Nat.pow_succ]))
      (add norm 0 (by grind only [Nat.succ_eq_add_one]))
      (add norm 0 (by grind only [Nat.succ_mul_succ]))
      (add norm 0 (by grind only [Nat.pow_succ']))
      (add norm 0 (by grind only [Nat.one_mul]))
      (add norm 0 (by grind only [Nat.mul_comm]))
      (add norm 0 (by grind only [Pell.xn_succ]))
      (add norm 0 (by grind only [Nat.left_distrib]))
      (add norm 0 (by grind only [Nat.succ_add_sub_one]))
      (add norm 0 (by grind only [Zsqrtd.SqLe]))
      (add norm 0 (by grind only [Nat.mul_assoc]))
      (add norm 0 (by grind only [Nat.succ_sub_succ]))
      (add norm 0 (by grind only [Nat.factorial_eq_mul_doubleFactorial]))
      (add norm 0 (by grind only [Nat.add_succ]))
      (add norm 0 (by grind only [Zsqrtd.sqLe_smul]))
      (add norm 0 (by grind only [Nat.fib_add]))
      (add norm 0 (by grind only [Nat.succ_mul_choose_eq]))
      (add norm 0 (by grind only [Nat.succ_add]))
      (add norm 0 (by grind only [Nat.add_sub_cancel]))
      (add norm 0 (by grind only [Pell.xn_succ_succ]))
      (add norm 0 (by grind only [Nat.choose_succ_right_eq]))

  -- Step 13 & 14: Parametrize a+1 and c+1
  -- Since 7 | 25*(c+1) and gcd(7,25)=1, then 7 | (c+1).
  -- Similarly, 25 | 7*(a+1) and gcd(25,7)=1, then 25 | (a+1).
  -- Let c+1 = 7k and a+1 = 25k.
  -- First, let's establish that (c+1) is divisible by 7.
  have h_c_div_7 : 7 ∣ (c + 1) := by
    clear * - h_ratio_eq
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by field_simp [*] at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.Prime.not_dvd_one]))
      (add norm 0 (by grind only [Pell.dvd_of_ysq_dvd]))
      (add norm 0 (by grind only [Nat.mul_dvd_mul_iff_left]))
      (add norm 0 (by grind only [Nat.Coprime.mul_dvd_of_dvd_of_dvd]))
      (add norm 0 (by grind only [Nat.dvd_iff_prime_pow_dvd_dvd]))
      (add norm 0 (by grind only [Nat.dvd_add]))
      (add norm 0 (by grind only [Nat.prime_two]))
      (add norm 0 (by grind only [dvd_mul_left]))
      (add norm 0 (by grind only [dvd_add]))
      (add norm 0 (by grind only [Nat.dvd_trans]))
      (add norm 0 (by grind only [Nat.ModEq.symm]))
      (add norm 0 (by grind only [ZMod.eisenstein_lemma_aux]))
      (add norm 0 (by grind only [Nat.dvd_add_right]))
      (add norm 0 (by grind only [Nat.dvd_two_of_totient_le_one]))
      (add norm 0 (by grind only [Nat.dvd_add_iff_right]))
      (add unsafe 10% (by grind only [Pell.xn]))
      (add unsafe 10% (by grind only [Pell.yn]))
      (add unsafe 10% (by grind only [Nat.le_of_dvd]))
      (add unsafe 10% (by grind only [dvd_trans]))
      (add unsafe 10% (by grind only [Pell.yn_modEq_two]))
      (add unsafe 10% (by grind only [Pell.y_dvd_iff]))
      (add unsafe 10% (by grind only [Pell.xy_coprime]))
      (add unsafe 10% (by grind only [Nat.dvd_factorial]))
      (add unsafe 10% (by grind only [Pell.xy_modEq_of_modEq]))
      (add unsafe 10% (by grind only [Nat.not_dvd_of_between_consec_multiples]))
      (add unsafe 10% (by grind only [Nat.dvd_sub]))
      (add unsafe 10% (by grind only [Pell.yn_ge_n]))
      (add unsafe 10% (by grind only [Pell.strictMono_y]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add unsafe 10% (by grind only [Pell.yn_modEq_a_sub_one]))
      (add unsafe 10% (by grind only [Nat.minSqFacAux_has_prop]))
      (add unsafe 10% (by grind only [Nat.minSqFacProp_div]))

  -- And (a+1) is divisible by 25.
  have h_a_div_25 : 25 ∣ (a + 1) := by
    clear * - h_ratio_eq
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by field_simp [*] at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.dvd_iff_prime_pow_dvd_dvd]))
      (add norm 0 (by grind only [Nat.Prime.dvd_of_dvd_pow]))
      (add norm 0 (by grind only [Nat.two_dvd_centralBinom_succ]))
      (add norm 0 (by grind only [Nat.mul_dvd_mul_iff_left]))
      (add norm 0 (by grind only [Equiv.Perm.two_dvd_card_support]))
      (add norm 0 (by grind only [Nat.Prime.not_dvd_one]))
      (add norm 0 (by grind only [ack_two]))
      (add unsafe 10% (by grind only [Nat.prime_two]))
      (add unsafe 10% (by grind only [Nat.le_of_dvd]))
      (add unsafe 10% (by grind only [LucasLehmer.two_lt_q]))
      (add unsafe 10% (by grind only [Nat.dvd_two_of_totient_le_one]))
      (add unsafe 10% (by grind only [Nat.dvd_factorial]))
      (add unsafe 10% (by grind only [dvd_trans]))
      (add unsafe 10% (by grind only [Pell.y_dvd_iff]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add unsafe 10% (by grind only [even_iff_two_dvd]))
      (add unsafe 10% (by grind only [Nat.not_dvd_of_between_consec_multiples]))
      (add unsafe 10% (by grind only [Pell.yn_modEq_two]))
      (add unsafe 10% (by grind only [Pell.xn]))
      (add unsafe 10% (by grind only [Pell.xy_coprime]))
      (add unsafe 10% (by grind only [Nat.succ_pos]))
      (add unsafe 10% (by grind only [Nat.minSqFacAux_has_prop]))
      (add unsafe 10% (by grind only [Pell.yn]))
      (add unsafe 10% (by grind only [Nat.mul_div_lt_iff_not_dvd]))
      (add unsafe 10% (by grind only [Pell.yn_ge_n]))
      (add unsafe 10% (by grind only [zero_lt_two]))
      (add unsafe 10% (by grind only [Nat.minSqFacProp_div]))
      (add unsafe 10% (by grind only [Pell.yn_modEq_a_sub_one]))
      (add unsafe 10% (by grind only [Pell.dvd_of_ysq_dvd]))
      (add unsafe 10% (by grind only [Nat.dvd_sub]))
      (add unsafe 10% (by grind only [Nat.not_dvd_of_pos_of_lt]))
      (add unsafe 10% (by grind only [Pell.xy_modEq_of_modEq]))

  -- Define k such that c + 1 = 7 * k
  obtain ⟨k, hk⟩ := h_c_div_7
  set k_def : c + 1 = 7 * k := hk
  -- Now express a + 1 in terms of k.
  -- From 7 * (a + 1) = 25 * (c + 1) = 25 * 7 * k => a + 1 = 25 * k.
  have h_a_eq : a + 1 = 25 * k := by
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 256
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.succ_pos]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [Nat.zero_lt_succ]))
      (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
      (add unsafe 10% (by grind only [Nat.succ_le_iff]))
      (add unsafe 10% (by grind only [Nat.le_succ]))
      (add unsafe 10% (by grind only [Nat.succ_le_succ]))
      (add unsafe 10% (by grind only [Nat.le_of_lt_succ]))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
      (add unsafe 10% (by grind only [Nat.succ_le]))
      (add unsafe 10% (by grind only [Nat.le_of_succ_le_succ]))
      (add unsafe 10% (by grind only [Nat.zero_le]))
      (add unsafe 10% (by grind only [Nat.le_succ_of_le]))
      (add unsafe 10% (by grind only [Nat.lt_succ_of_le]))
      (add unsafe 10% (by grind only [Nat.le_add_left]))
      (add unsafe 10% (by grind only [Ordnode.ratio]))
      (add unsafe 10% (by grind only [Ordnode.Valid'.rotateL_lemma₂]))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_right]))
      (add unsafe 10% (by grind only [Nat.lt_of_succ_le]))
      (add unsafe 10% (by grind only [Ordnode.Sized.pos]))
      (add unsafe 10% (by grind only [Pell.xn]))
      (add unsafe 10% (by grind only [Nat.lt_succ]))
      (add unsafe 10% (by grind only [Pell.x_pos]))
      (add unsafe 10% (by grind only [Nat.mod_lt]))
      (add unsafe 10% (by grind only [Pell.d_pos]))
      (add unsafe 10% (by grind only [Nat.succ_lt_succ]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₃]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₄]))
      (add unsafe 10% (by grind only [Pell.strictMono_x]))
      (add unsafe 10% (by grind only [Nat.le_div_iff_mul_le]))
      (add unsafe 10% (by grind only [Nat.le_add_right]))

  -- Update the definition of k usage if needed, but 'have' with equality is sufficient for rewriting.
  -- Let's explicitly state k is a natural number and positive.
  have h_k_pos : k > 0 := by
    -- Since c >= 0, c+1 >= 1. Thus 7*k >= 1, so k >= 1.
    clear * - hk
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by grind only [Nat.succ_pos]))
      (add unsafe 10% (by grind only [Pell.x_pos]))
      (add unsafe 10% (by grind only [Nat.lt_mul_div_succ]))
      (add unsafe 10% (by grind only [Nat.mul_pos]))
      (add unsafe 10% (by grind only [Nat.mul_lt_mul_left]))
      (add unsafe 10% (by grind only [Nat.mul_lt_mul_right]))
      (add unsafe 10% (by grind only [Nat.zero_le]))
      (add unsafe 10% (by grind only [Pell.d_pos]))
      (add unsafe 10% (by grind only [Nat.le_of_lt_succ]))
      (add unsafe 10% (by grind only [Nat.zero_lt_succ]))
      (add unsafe 10% (by grind only [Ordnode.Sized.pos]))
      (add unsafe 10% (by grind only [Nat.nat_repr_len_aux]))
      (add unsafe 10% (by grind only [Nat.div_lt_self]))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
      (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
      (add unsafe 10% (by grind only [Nat.div_lt_iff_lt_mul]))
      (add unsafe 10% (by grind only [Nat.mul_lt_mul_of_pos_left]))
      (add unsafe 10% (by grind only [Nat.succ_le_succ]))
      (add unsafe 10% (by grind only [Pell.eq_pow_of_pell_lem]))
      (add unsafe 10% (by grind only [Nat.div_lt_iff_lt_mul']))
      (add unsafe 10% (by grind only [Nat.succ_le_iff]))
      (add unsafe 10% (by grind only [Nat.lt_two_pow]))
      (add unsafe 10% (by grind only [Nat.lt_of_succ_le]))
      (add unsafe 10% (by grind only [Nat.le_mul_of_pos_left]))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_right]))
      (add unsafe 10% (by grind only [Nat.le_succ]))
      (add unsafe 10% (by grind only [Ordnode.Valid'.rotateL_lemma₂]))
      (add unsafe 10% (by grind only [Nat.mul_lt_mul_pow_succ]))
      (add unsafe 10% (by grind only [Nat.pow_pos]))
      (add unsafe 10% (by grind only [Nat.sub_lt]))
      (add unsafe 10% (by grind only [Nat.le_of_succ_le_succ]))
      (add unsafe 10% (by grind only [Nat.le_div_iff_mul_le]))

  -- Step 15 & 16: Express b+1 in terms of k.
  -- (a+1)(b+1) = 525 => 25k * (b+1) = 525 => b+1 = 525 / 25k = 21/k.
  -- This implies k divides 21.
  have h_b_plus_one : (b + 1) * k = 21 := by
    -- From h₁': (a+1)*(b+1) = 525.
    -- Substitute a+1 = 25k.
    -- 25k * (b+1) = 525.
    -- Divide by 25: k * (b+1) = 21.
    clear * - h₁' h_a_eq
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 256
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
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
      (add norm 0 (by grind only [Nat.succ_pos]))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [Nat.mul_le_mul_right]))
      (add norm 0 (by grind only [Nat.succ_le_succ]))
      (add norm 0 (by grind only [Nat.mul_succ]))
      (add norm 0 (by grind only [Zsqrtd.SqLe]))
      (add norm 0 (by grind only [Nat.le_add_left]))
      (add norm 0 (by grind only [Nat.pow_succ]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Nat.zero_lt_succ]))
      (add norm 0 (by grind only [SimpleGraph.aux]))
      (add norm 0 (by grind only [Nat.one_mul]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Nat.pow_succ']))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
      (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
      (add unsafe 10% (by grind only [Nat.zero_le]))
      (add unsafe 10% (by grind only [Nat.le_of_lt_succ]))
      (add unsafe 10% (by grind only [Nat.succ_le_iff]))
      (add unsafe 10% (by grind only [Nat.le_succ]))
      (add unsafe 10% (by grind only [Nat.le_of_succ_le_succ]))
      (add unsafe 50% (by nlinarith [Ordnode.ratio]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add unsafe 10% (by grind only [Nat.succ_le]))
      (add unsafe 10% (by grind only [Pell.xn]))
      (add unsafe 10% (by grind only [Nat.le_div_iff_mul_le]))
      (add unsafe 10% (by grind only [Nat.le_mul_of_pos_left]))
      (add unsafe 10% (by grind only [Nat.mod_lt]))
      (add unsafe 10% (by grind only [Ordnode.Sized.pos]))
      (add unsafe 10% (by grind only [Pell.d_pos]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₂]))
      (add unsafe 10% (by grind only [Nat.div_lt_self]))

  -- Step 17 & 18: Express d+1 in terms of k.
  -- (c+1)(d+1) = 105 => 7k * (d+1) = 105 => k * (d+1) = 15.
  have h_d_plus_one : (d + 1) * k = 15 := by
    -- From h₃': (c+1)*(d+1) = 105.
    -- Substitute c+1 = 7k.
    -- 7k * (d+1) = 105.
    -- Divide by 7: k * (d+1) = 15.
    clear * - h₃' hk
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 256
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 0 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.succ_mul]))
      (add norm 0 (by grind only [Nat.mul_one]))
      (add norm 0 (by grind only [Nat.mul_succ]))
      (add norm 0 (by grind only [Nat.succ_eq_add_one]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Nat.succ_pos]))
      (add norm 0 (by grind only [Nat.succ_ne_zero]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [Nat.factorial_succ]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Nat.pow_succ']))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [Nat.superFactorial_succ]))
      (add norm 0 (by grind only [Nat.succ_sub_succ]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Nat.succ_add_sub_one]))
      (add norm 0 (by grind only [Nat.succ_le_succ]))
      (add norm 0 (by grind only [Nat.zero_lt_succ]))
      (add norm 0 (by grind only [Nat.one_mul]))
      (add norm 0 (by grind only [Num.cast_succ]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Nat.le_succ]))
      (add norm 0 (by grind only [Nat.zero_le]))
      (add norm 0 (by grind only [Nat.pow_succ]))
      (add norm 0 (by grind only [Nat.succ_sub_one]))
      (add norm 0 (by grind only [Pell.xn_succ]))
      (add norm 0 (by grind only [Nat.succ_sub_succ_eq_sub]))
      (add norm 0 (by grind only [Nat.add_succ_sub_one]))
      (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add unsafe 10% (by grind only [Nat.succ_le_iff]))
      (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))

  -- Step 19, 20, 21, 22, 23: Determine possible values of k.
  -- k divides 21 and k divides 15. So k divides gcd(21, 15) = 3.
  have h_k_div_gcd : k ∣ 3 := by
    have h_div_21 : k ∣ 21 := by
      -- From h_b_plus_one: (b+1)*k = 21. So k divides 21.
      clear * - h_b_plus_one
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        enableUnfold := false
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by positivity))
        (add norm 0 (by omega))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 100 (by ring_nf at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by field_simp [*] at *))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [dvd_mul_left]))
        (add norm 0 (by grind only [Nat.Coprime.mul_dvd_of_dvd_of_dvd]))
        (add norm 0 (by grind only [Pell.ysq_dvd_yy]))
        (add norm 0 (by grind only [Nat.Coprime.dvd_mul_left]))
        (add norm 0 (by grind only [Pell.y_mul_dvd]))
        (add norm 0 (by grind only [dvd_mul_right]))
        (add norm 0 (by grind only [Nat.mul_dvd_mul_iff_left]))
        (add norm 0 (by grind only [Nat.dvd_trans]))
        (add norm 0 (by grind only [Nat.Prime.dvd_mul]))
        (add norm 0 (by grind only [Nat.dvd_mul_left]))
        (add norm 0 (by grind only [Prime.dvd_or_dvd]))
        (add norm 0 (by grind only [Nat.Coprime.dvd_of_dvd_mul_left]))
        (add norm 0 (by grind only [Nat.Coprime.dvd_of_dvd_mul_right]))
        (add norm 0 (by grind only [IsPrimitiveRoot.dvd_of_isCyclotomicExtension]))
        (add norm 0 (by grind only [Nat.dvd_mul_right]))
        (add norm 0 (by grind only [mul_dvd_mul_left]))
        (add norm 0 (by grind only [Nat.dvd_gcd]))
        (add norm 0 (by grind only [Nat.Coprime.dvd_mul_right]))
        (add norm 0 (by grind only [Nat.mul_dvd_mul_left]))
        (add norm 0 (by grind only [Nat.dvd_of_mul_dvd_mul_left]))
        (add norm 0 (by grind only [mul_dvd_mul]))
        (add norm 0 (by grind only [Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd]))
        (add norm 0 (by grind only [Nat.dvd_add]))
        (add norm 0 (by grind only [Prime.dvd_mul]))
        (add norm 0 (by grind only [mul_dvd_mul_iff_left]))
        (add norm 0 (by grind only [Nat.mul_dvd_mul]))
        (add unsafe 10% (by grind only [Pell.dvd_of_ysq_dvd]))
        (add unsafe 10% (by grind only [Pell.yn]))
        (add unsafe 10% (by grind only [Pell.xn]))
        (add unsafe 10% (by grind only [Pell.yn_modEq_two]))
        (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
        (add unsafe 10% (by grind only [Pell.xy_coprime]))

    have h_div_15 : k ∣ 15 := by
      -- From h_d_plus_one: (d+1)*k = 15. So k divides 15.
      clear * - h_d_plus_one
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 100 (by gcongr))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 100 (by exfalso))
        (add norm 100 (by ring_nf at *))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by push_neg))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by rfl))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Nat.dvd_mul_left]))
        (add norm 0 (by grind only [Nat.dvd_mul_right]))
        (add norm 0 (by grind only [Nat.mul_dvd_mul_left]))
        (add norm 0 (by grind only [Nat.dvd_add]))
        (add norm 0 (by grind only [Nat.Coprime.dvd_mul_left]))
        (add norm 0 (by grind only [Nat.Coprime.dvd_of_dvd_mul_right]))
        (add norm 0 (by grind only [Nat.dvd_trans]))
        (add norm 0 (by grind only [Nat.mul_dvd_mul]))
        (add norm 0 (by grind only [Nat.mul_one]))
        (add norm 0 (by grind only [Nat.Coprime.dvd_of_dvd_mul_left]))
        (add norm 0 (by grind only [Nat.Coprime.mul_dvd_of_dvd_of_dvd]))
        (add norm 0 (by grind only [Nat.mul_add]))
        (add norm 0 (by grind only [Nat.dvd_add_iff_left]))
        (add norm 0 (by grind only [Nat.Coprime.dvd_mul_right]))
        (add norm 0 (by grind only [Nat.eq_one_of_dvd_one]))
        (add norm 0 (by grind only [Nat.dvd_add_iff_right]))
        (add norm 0 (by grind only [Nat.dvd_refl]))
        (add norm 0 (by grind only [Nat.left_distrib]))
        (add norm 0 (by grind only [Nat.mul_comm]))
        (add norm 0 (by grind only [Nat.mul_succ]))
        (add norm 0 (by grind only [Nat.Prime.dvd_mul]))
        (add norm 0 (by grind only [Nat.prod_factorial_dvd_factorial_sum]))
        (add norm 0 (by grind only [Nat.succ_mul]))
        (add norm 0 (by grind only [Nat.dvd_gcd]))
        (add norm 0 (by grind only [Nat.one_mul]))
        (add norm 0 (by grind only [Nat.mul_assoc]))
        (add norm 0 (by grind only [Nat.mul_dvd_mul_iff_left]))
        (add norm 0 (by grind only [Nat.add_mul]))
        (add norm 0 (by grind only [Pell.y_mul_dvd]))
        (add norm 0 (by grind only [Pell.ysq_dvd_yy]))
        (add norm 0 (by grind only [Nat.factorization_eq_zero_iff_remainder]))
        (add norm 0 (by grind only [Prime.dvd_mul]))

    -- k divides both 21 and 15.
    clear * - h_div_21 h_div_15
    have : k ≤ 21 := Nat.le_of_dvd (by decide) h_div_21
    interval_cases k <;> simp_all (config := { decide := true }) [h_div_21, h_div_15]

  -- Possible values for k are divisors of 3: 1 and 3.
  have h_k_val : k = 1 ∨ k = 3 := by
    clear * - h_k_div_gcd h_k_pos
    have h_k : k ≤ 3
    · exact Nat.le_of_dvd (by decide) h_k_div_gcd
    · interval_cases k <;> (simp_all)

  -- Step 25, 26, 27, 28, 29: Use the product constraint h₀ to determine k.
  -- a = 25k - 1, b = 21/k - 1, c = 7k - 1, d = 15/k - 1.
  -- Product a*b*c*d = 8! = 40320.
  -- Let's compute the product for each case.
  cases h_k_val with
  | inl h_k_1 =>
    have h_k_is_1 : k = 1 := h_k_1
    -- If k=1:
    -- a+1 = 25 => a = 24
    -- b+1 = 21 => b = 20
    -- c+1 = 7 => c = 6
    -- d+1 = 15 => d = 14
    have h_a_val : a = 24 := by
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        maxGoals := 256
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 0 (by positivity))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Nat.succ_pos]))
        (add norm 0 (by grind only [Iff]))
        (add norm 0 (by grind only [Nat.prime_two]))
        (add norm 0 (by grind only [two_mul]))
        (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
        (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
        (add unsafe 10% (by grind only [Nat.mod_lt]))
        (add unsafe 10% (by grind only [Pell.xn]))
        (add unsafe 10% (by grind only [Pell.x_pos]))
        (add unsafe 10% (by grind only [Nat.le_of_dvd]))
        (add unsafe 10% (by grind only [Pell.d_pos]))
        (add unsafe 10% (by grind only [Pell.strictMono_x]))
        (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
        (add unsafe 10% (by grind only [LucasLehmer.two_lt_q]))
        (add unsafe 10% (by grind only [Pell.strictMono_y]))
        (add unsafe 10% (by grind only [Or.resolve_left]))
        (add unsafe 10% (by grind only [mul_left_cancel₀]))
        (add unsafe 10% (by grind only [Nat.pos_of_ne_zero]))
        (add unsafe 10% (by grind only [Pell.yn_ge_n]))
        (add unsafe 10% (by grind only [Ordnode.Sized.pos]))
        (add unsafe 10% (by grind only [Nat.zero_le]))
        (add unsafe 10% (by grind only [Pell.eq_pow_of_pell_lem]))
        (add unsafe 10% (by grind only [zero_lt_two]))
        (add unsafe 10% (by grind only [Pell.yn]))
        (add unsafe 10% (by grind only [Ordnode.ratio]))
        (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem3]))
        (add unsafe 10% (by grind only [Nat.succ_le_iff]))
        (add unsafe 10% (by grind only [lt_of_le_of_ne]))
        (add unsafe 10% (by grind only [Nat.mul_div_lt_iff_not_dvd]))
        (add unsafe 10% (by grind only [Nat.succ_le]))
        (add unsafe 10% (by grind only [Nat.le_of_lt_succ]))
        (add unsafe 10% (by grind only [le_of_mul_le_mul_right]))

    have h_b_val : b = 20 := by
      have hb : (b + 1) * 1 = 21 := by rw [h_k_is_1] at h_b_plus_one; exact h_b_plus_one
      omega

    have h_c_val : c = 6 := by
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        maxGoals := 256
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 0 (by positivity))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Nat.succ_pos]))
        (add norm 0 (by grind only [Iff]))
        (add norm 0 (by grind only [dvd_mul_left]))
        (add norm 0 (by grind only [mul_left_comm]))
        (add norm 0 (by grind only [mul_comm]))
        (add unsafe 10% (by grind only [Pell.xn]))
        (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
        (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
        (add unsafe 10% (by grind only [Nat.le_of_dvd]))
        (add unsafe 10% (by grind only [Pell.x_pos]))
        (add unsafe 10% (by grind only [Nat.mod_lt]))
        (add unsafe 10% (by grind only [mul_left_cancel₀]))
        (add unsafe 10% (by grind only [Pell.strictMono_x]))
        (add unsafe 10% (by grind only [Pell.d_pos]))
        (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
        (add unsafe 10% (by grind only [Pell.yn_ge_n]))
        (add unsafe 10% (by grind only [Nat.div_lt_self]))
        (add unsafe 10% (by grind only [Pell.strictMono_y]))
        (add unsafe 10% (by grind only [Nat.mul_div_lt_iff_not_dvd]))
        (add unsafe 10% (by grind only [Pell.yn]))
        (add unsafe 10% (by grind only [Nat.succ_le_iff]))
        (add unsafe 10% (by grind only [Pell.eq_pow_of_pell_lem]))
        (add unsafe 10% (by grind only [Pell.pell_eq]))
        (add unsafe 10% (by grind only [Nat.pos_of_ne_zero]))
        (add unsafe 10% (by grind only [mul_right_inj']))
        (add unsafe 10% (by grind only [Nat.le_of_lt_succ]))
        (add unsafe 10% (by grind only [LucasLehmer.two_lt_q]))
        (add unsafe 10% (by grind only [Nat.succ_le]))
        (add unsafe 10% (by grind only [Nat.zero_le]))
        (add unsafe 10% (by grind only [Pell.yn_modEq_a_sub_one]))
        (add unsafe 10% (by grind only [SimpleGraph.aux]))
        (add unsafe 10% (by grind only [Ordnode.Sized.pos]))

    have h_d_val : d = 14 := by
      have hd : (d + 1) * 1 = 15 := by rw [h_k_is_1] at h_d_plus_one; exact h_d_plus_one
      omega

    -- Check if this satisfies h₀: a*b*c*d = 40320
    -- 24 * 20 * 6 * 14 = 480 * 84 = 40320. Correct.
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by positivity))
      (add norm 0 (by grind only [Pell.x_sub_y_dvd_pow]))
      (add norm 0 (by grind only [Int.ofNat_sub]))
      (add norm 0 (by grind only [ZMod.intCast_zmod_eq_zero_iff_dvd]))
      (add norm 0 (by grind only [ZMod.natCast_zmod_eq_zero_iff_dvd]))
      (add norm 0 (by grind only [Int.natCast_modEq_iff]))
      (add norm 0 (by grind only [div_eq_one]))
      (add norm 0 (by grind only [div_eq_iff_eq_mul']))
      (add norm 0 (by grind only [ZMod.natCast_zmod_val]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [Nat.cast_sub]))
      (add norm 0 (by grind only [ZMod.intCast_eq_intCast_iff_dvd_sub]))
      (add norm 0 (by grind only [Pell.xz]))
      (add norm 0 (by grind only [Nat.cast_add]))
      (add norm 0 (by grind only [ZMod.natCast_self]))
      (add norm 0 (by grind only [eq_div_iff_mul_eq']))
      (add norm 0 (by grind only [Nat.modEq_iff_dvd]))
      (add norm 0 (by grind only [Int.modEq_iff_dvd]))
      (add norm 0 (by grind only [LucasLehmer.Int.coe_nat_two_pow_pred]))
      (add norm 0 (by rw [Int.ofNat_add]))
      (add norm 0 (by grind only [Int.natCast_sub]))
      (add norm 0 (by grind only [Pell.yz]))
      (add norm 0 (by rw [Nat.cast_one]))
      (add norm 0 (by grind only [ZMod.natCast_eq_natCast_iff]))
      (add norm 0 (by grind only [ZMod.val]))
      (add norm 0 (by grind only [Nat.cast_pow]))
      (add safe 1 (by simp_all only [div_eq_iff_eq_mul]))
      (add safe 0 (by simp_all [Int.cast_sub]))
      (add safe 0 (by simp_all [Int.cast_inj]))
      (add unsafe 50% (by rw [← Int.natCast_inj] at *))
      (add unsafe 50% (by rw [← Nat.cast_inj] at *))
      (add unsafe 50% (by rw [← Int.ofNat_inj] at *))
      (add unsafe 50% (by rw [← Int.natCast_pow] at *))

  | inr h_k_3 =>
    have h_k_is_3 : k = 3 := h_k_3
    -- If k=3:
    -- a+1 = 75 => a = 74
    -- c+1 = 21 => c = 20
    -- b+1 = 21/3 = 7 => b = 6
    -- d+1 = 15/3 = 5 => d = 4
    have h_a_val : a = 74 := by
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 0 (by positivity))
        (add safe 100 (by push_neg))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Iff]))
        (add unsafe 10% (by grind only [Nat.le_of_dvd]))
        (add unsafe 10% (by grind only [Pell.x_pos]))
        (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
        (add unsafe 10% (by grind only [Pell.xn]))
        (add unsafe 10% (by grind only [Pell.yn_ge_n]))
        (add unsafe 10% (by grind only [Pell.strictMono_y]))
        (add unsafe 10% (by grind only [Pell.strictMono_x]))
        (add unsafe 10% (by grind only [Nat.mul_div_lt_iff_not_dvd]))
        (add unsafe 10% (by grind only [Pell.eq_pow_of_pell_lem]))
        (add unsafe 10% (by grind only [Pell.yn_modEq_a_sub_one]))
        (add unsafe 10% (by grind only [Pell.d_pos]))
        (add unsafe 10% (by grind only [Nat.pos_of_ne_zero]))
        (add unsafe 10% (by grind only [Pell.yn]))
        (add unsafe 10% (by grind only [Pell.xy_coprime]))
        (add unsafe 10% (by grind only [lt_of_le_of_ne]))
        (add unsafe 10% (by grind only [Pell.pell_eq]))
        (add unsafe 10% (by grind only [Ordnode.Sized.pos]))
        (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
        (add unsafe 10% (by grind only [Nat.mod_lt]))
        (add unsafe 10% (by grind only [Nat.dvd_sub]))
        (add unsafe 10% (by grind only [Nat.minSqFacProp_div]))
        (add unsafe 10% (by grind only [LucasLehmer.two_lt_q]))
        (add unsafe 10% (by grind only [Pell.yn_modEq_two]))
        (add unsafe 10% (by grind only [dvd_trans]))
        (add unsafe 10% (by grind only [Nat.succ_pos]))
        (add unsafe 10% (by grind only [Pell.xy_modEq_of_modEq]))
        (add unsafe 10% (by grind only [Nat.div_lt_self]))
        (add unsafe 10% (by grind only [Or.resolve_left]))
        (add unsafe 10% (by grind only [Nat.lt_of_succ_le]))
        (add unsafe 10% (by grind only [Nat.dvd_factorial]))
        (add unsafe 10% (by grind only [le_of_mul_le_mul_right]))

    have h_b_val : b = 6 := by
      have hb : (b + 1) * 3 = 21 := by rw [h_k_is_3] at h_b_plus_one; exact h_b_plus_one
      omega

    have h_c_val : c = 20 := by
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        maxGoals := 256
        useDefaultSimpSet := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
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
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [Eq.symm]))
        (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
        (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
        (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
        (add unsafe 10% (by grind only [zero_lt_two]))
        (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
        (add unsafe 10% (by grind only [LucasLehmer.two_lt_q]))
        (add unsafe 10% (by grind only [Pell.x_pos]))
        (add unsafe 10% (by grind only [Nat.le_of_dvd]))
        (add unsafe 10% (by grind only [SimpleGraph.aux]))
        (add unsafe 10% (by grind only [Nat.mod_lt]))
        (add unsafe 10% (by grind only [Pell.xn]))
        (add unsafe 10% (by grind only [Nat.div_lt_self]))
        (add unsafe 10% (by grind only [Nat.prime_two]))
        (add unsafe 10% (by grind only [Pell.strictMono_x]))
        (add unsafe 10% (by grind only [Nat.succ_pos]))
        (add unsafe 10% (by grind only [Pell.eq_pow_of_pell_lem]))
        (add unsafe 10% (by grind only [Pell.d_pos]))
        (add unsafe 10% (by grind only [Nat.pos_of_ne_zero]))
        (add unsafe 10% (by grind only [mul_left_cancel₀]))
        (add unsafe 10% (by grind only [Pell.strictMono_y]))
        (add unsafe 10% (by grind only [Pell.yn_ge_n]))
        (add unsafe 10% (by grind only [Nat.mul_div_lt_iff_not_dvd]))
        (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem3]))
        (add unsafe 10% (by grind only [one_lt_two]))
        (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
        (add unsafe 10% (by grind only [Pell.pell_eq]))
        (add unsafe 10% (by grind only [Pell.yn]))
        (add unsafe 10% (by grind only [Nat.le_of_lt_succ]))
        (add unsafe 10% (by grind only [gold_lt_two]))
        (add unsafe 10% (by grind only [Nat.add_div]))

    have h_d_val : d = 4 := by
      have hd : (d + 1) * 3 = 15 := by rw [h_k_is_3] at h_d_plus_one; exact h_d_plus_one
      omega

    -- Check product: 74 * 6 * 20 * 4 = 74 * 480 = 35520.
    -- But 8! = 40320. Contradiction.
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
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by positivity))
      (add norm 0 (by grind only [div_eq_one]))
      (add norm 0 (by grind only [Pell.x_sub_y_dvd_pow]))
      (add norm 0 (by grind only [eq_div_iff_mul_eq']))
      (add norm 0 (by grind only [Int.ofNat_sub]))
      (add norm 0 (by grind only [ZMod.intCast_zmod_eq_zero_iff_dvd]))
      (add norm 0 (by grind only [Int.natCast_modEq_iff]))
      (add norm 0 (by grind only [eq_div_iff_mul_eq]))
      (add norm 0 (by grind only [Int.modEq_iff_dvd]))
      (add norm 0 (by grind only [ZMod.natCast_zmod_eq_zero_iff_dvd]))
      (add norm 0 (by grind only [ZMod.intCast_eq_intCast_iff_dvd_sub]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_xa]))
      (add norm 0 (by grind only [Nat.cast_sub]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [Nat.modEq_iff_dvd]))
      (add norm 0 (by grind only [LucasLehmer.Int.coe_nat_two_pow_pred]))
      (add norm 0 (by grind only [Pell.xz]))
      (add norm 0 (by grind only [Nat.cast_add]))
      (add norm 0 (by grind only [ZMod.natCast_zmod_val]))
      (add norm 0 (by grind only [eq_div_iff]))
      (add norm 0 (by grind only [Nat.cast_inj]))
      (add norm 0 (by grind only [Int.natCast_sub]))
      (add norm 0 (by grind only [div_eq_iff]))
      (add norm 0 (by grind only [mul_div_cancel_right]))
      (add norm 0 (by rw [Int.ofNat_add]))
      (add norm 0 (by grind only [AddCommGroup.modEq_iff_int_modEq]))
      (add safe 1 (by simp_all only [div_eq_iff_eq_mul]))
      (add safe 1 (by simp_all only [div_eq_iff_eq_mul']))
      (add safe 0 (by simp_all [Int.cast_sub]))
      (add safe 0 (by simp_all [Int.cast_inj]))
      (add unsafe 50% (by rw [← Int.natCast_inj] at *))
      (add unsafe 50% (by rw [← Int.ofNat_inj] at *))
