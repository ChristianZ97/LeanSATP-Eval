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


theorem mathd_numbertheory_1124 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 18 ∣ 374 * 10 + n) : n = 4 := by

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
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by push_neg))
    (add safe 100 (by zify))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 10% (by grind only [Nat.le_of_dvd]))
    (add unsafe 10% (by grind only [Nat.pos_of_ne_zero]))
    (add unsafe 10% (by grind only [Nat.dvd_two_of_totient_le_one]))
    (add unsafe 10% (by grind only [pos_of_gt]))
    (add unsafe 10% (by grind only [Pell.x_pos]))
    (add unsafe 10% (by grind only [Nat.mod_lt]))
    (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
    (add unsafe 10% (by grind only [Nat.pos_of_dvd_of_pos]))
    (add unsafe 10% (by grind only [Nat.Prime.one_lt]))
    (add unsafe 10% (by grind only [Nat.mul_div_lt_iff_not_dvd]))
    (add unsafe 10% (by grind only [Nat.not_dvd_of_pos_of_lt]))
    (add unsafe 10% (by grind only [Nat.one_le_of_lt]))
    (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
    (add unsafe 10% (by grind only [Zsqrtd.d_pos]))
    (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem3]))
    (add unsafe 10% (by grind only [ascPochhammer_pos]))
    (add unsafe 10% (by grind only [Nat.dvd_factorial]))
    (add unsafe 10% (by grind only [lt_of_le_of_ne]))
    (add unsafe 10% (by grind only [LucasLehmer.two_lt_q]))
    (add unsafe 10% (by grind only [IsPrimePow.one_lt]))
    (add unsafe 10% (by grind only [Nat.Prime.two_le]))
    (add unsafe 10% (by grind only [le_self_pow]))
    (add unsafe 10% (by grind only [Nat.exists_eq_succ_of_ne_zero]))
    (add unsafe 10% (by grind only [le_of_mul_le_mul_right]))
    (add unsafe 10% (by grind only [Nat.eq_zero_of_dvd_of_lt]))
    (add unsafe 10% (by grind only [Pell.yn_ge_n]))
    (add unsafe 10% (by grind only [Nat.factorization_le_iff_dvd]))
    (add unsafe 10% (by grind only [Nat.totient_pos]))
    (add unsafe 10% (by grind only [Nat.not_dvd_of_between_consec_multiples]))
    (add unsafe 10% (by grind only [mul_le_iff_le_one_left]))
    (add unsafe 10% (by grind only [Pell.eq_pow_of_pell_lem]))
    (add unsafe 10% (by grind only [Nat.not_eq_zero_of_lt]))
