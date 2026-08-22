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


theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by

  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    maxGoals := 16
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 100 (by exfalso))
    (add norm 0 (by ring_nf at *))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by ext))
    (add safe 0 (by split))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Nat.add_mod]))
    (add norm 0 (by grind only [Nat.add_mod_left]))
    (add norm 0 (by grind only [Nat.mul_add_mod]))
    (add norm 0 (by grind only [Nat.add_mod_mod]))
    (add norm 0 (by grind only [Nat.add_mod_right]))
    (add norm 0 (by grind only [Nat.mod_add_mod]))
    (add norm 0 (by grind only [Nat.mod_self]))
    (add norm 0 (by grind only [PNat.XgcdType.r]))
    (add norm 0 (by grind only [Nat.mod_succ]))
    (add norm 0 (by grind only [Nat.mul_add_mod']))
    (add norm 0 (by grind only [Nat.mod_eq_of_lt]))
    (add norm 0 (by grind only [Nat.mod_add_div]))
    (add norm 0 (by grind only [Nat.add_mod_add_ite]))
    (add norm 0 (by grind only [Nat.add_mul_mod_self_left]))
    (add norm 0 (by grind only [Nat.mod_mul_right_mod]))
    (add norm 0 (by grind only [Nat.div_add_mod]))
    (add norm 0 (by grind only [Nat.mod_succ_eq_iff_lt]))
    (add norm 0 (by grind only [Nat.one_mod]))
    (add norm 0 (by grind only [Nat.mod_two_add_succ_mod_two]))
    (add norm 0 (by grind only [Nat.mod_injOn_Ico]))
    (add norm 0 (by grind only [Nat.add_mod_eq_add_mod_right]))
    (add norm 0 (by grind only [Fin.val_add]))
    (add norm 0 (by grind only [Nat.add_mod_of_add_mod_lt]))
    (add norm 0 (by grind only [Fin.coe_modNat]))
    (add unsafe 50% (by nlinarith [Nat.mod_mod]))
    (add unsafe 50% (by nlinarith [Nat.mod_mul_left_mod]))
    (add unsafe 50% (by nlinarith [Nat.mul_mod]))
    (add unsafe 50% (by nlinarith [Nat.dvd_iff_mod_eq_zero]))
    (add unsafe 50% (by nlinarith [Nat.mod_eq_zero_of_dvd]))
    (add unsafe 50% (by nlinarith [Nat.mod_mod_of_dvd]))
    (add unsafe 50% (by nlinarith [Nat.ModEq]))
    (add unsafe 50% (by nlinarith [Nat.mul_mod_mul_left]))
