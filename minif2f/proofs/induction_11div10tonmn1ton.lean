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


theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by

  aesop (config := {
    maxRuleApplications := 1600
    maxNormIterations := 320
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by omega))
    (add norm 100 (by gcongr))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 100 (by ring_nf at *))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by push_neg))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [QuaternionGroup.a_one_pow]))
    (add norm 0 (by grind only [DihedralGroup.r_one_pow]))
    (add norm 0 (by grind only [one_pow]))
    (add norm 0 (by grind only [QuaternionGroup.one_def]))
    (add norm 0 (by rw [DihedralGroup.r_one_pow_n]))
    (add norm 0 (by grind only [sub_dvd_pow_sub_pow]))
    (add norm 0 (by grind only [ArithmeticFunction.moebius_apply_of_squarefree]))
    (add norm 0 (by grind only [Nat.Prime.not_dvd_one]))
    (add norm 0 (by grind only [Nat.dvd_one]))
    (add norm 0 (by grind only [nat_sub_dvd_pow_sub_pow]))
    (add norm 0 (by grind only [orderOf_dvd_iff_pow_eq_one]))
    (add norm 0 (by grind only [Even.neg_one_pow]))
    (add norm 0 (by grind only [Nat.eq_one_of_dvd_coprimes]))
    (add norm 0 (by grind only [Commute.pow_dvd_sub_pow_of_pow_eq_zero_left]))
    (add norm 0 (by grind only [DihedralGroup.one_def]))
    (add norm 0 (by grind only [pow_one]))
    (add norm 0 (by grind only [orderOf_dvd_of_pow_eq_one]))
    (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_one]))
    (add norm 0 (by grind only [AlgebraicGeometry.Proj.pow_apply]))
    (add norm 0 (by grind only [QuaternionGroup.a_one_pow_n]))
    (add norm 0 (by grind only [one_dvd]))
    (add norm 0 (by grind only [dvd_refl]))
    (add norm 0 (by grind only [Commute.pow_dvd_sub_pow_of_pow_eq_zero_right]))
    (add norm 0 (by grind only [ArithmeticFunction.cardDistinctFactors_apply_prime_pow]))
    (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
    (add norm 0 (by grind only [Commute.one_right]))
    (add norm 0 (by grind only [neg_one_sq]))
    (add norm 0 (by grind only [legendreSym.at_one]))
    (add norm 0 (by grind only [legendreSym.prime_dvd_of_eq_neg_one]))
    (add norm 0 (by grind only [jacobiSym.prime_dvd_of_eq_neg_one]))
    (add norm 0 (by grind only [Nat.eq_one_of_dvd_one]))
    (add norm 0 (by grind only [Prime.not_dvd_one]))
