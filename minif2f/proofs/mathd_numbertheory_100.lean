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


theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by omega))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by interval_cases))
    (add safe 100 (by ring_nf))
    (add safe 0 (by split))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Nat.gcd_pos_of_pos_left]))
    (add norm 0 (by grind only [Nat.gcd_ne_zero_right]))
    (add norm 0 (by grind only [Nat.gcd_ne_zero_left]))
    (add norm 0 (by grind only [Nat.lcm_pos]))
    (add norm 0 (by grind only [Nat.gcd_eq_right]))
    (add norm 0 (by grind only [Nat.gcd_eq_left]))
    (add norm 0 (by grind only [Nat.gcd_dvd_left]))
    (add norm 0 (by grind only [Nat.gcd_dvd_right]))
    (add norm 0 (by grind only [Nat.lcm]))
    (add norm 0 (by grind only [Int.gcd]))
    (add norm 0 (by grind only [Nat.factorization_lcm]))
    (add norm 0 (by grind only [jacobiSym.ne_zero]))
    (add norm 0 (by grind only [Nat.gcd_eq_zero_iff]))
    (add norm 0 (by grind only [ZMod.addOrderOf_coe]))
    (add norm 0 (by grind only [Nat.exists_mul_emod_eq_gcd]))
    (add norm 0 (by grind only [Nat.factorization_gcd]))
    (add norm 0 (by grind only [PNat.lcm]))
    (add norm 0 (by grind only [Nat.gcd_le_left]))
    (add norm 0 (by grind only [ZMod.ne_zero_of_gcd_eq_one]))
    (add norm 0 (by grind only [Nat.lcm_ne_zero]))
    (add norm 0 (by grind only [PNat.gcd]))
    (add norm 0 (by grind only [Int.coe_gcd]))
    (add norm 0 (by grind only [orderOf_pow']))
    (add norm 0 (by grind only [Nat.gcd]))
    (add norm 0 (by grind only [Nat.gcd_greatest]))
    (add norm 0 (by grind only [jacobiSym.sq_one']))
    (add norm 0 (by grind only [Nat.eq_of_dvd_of_div_eq_one]))
    (add norm 0 (by grind only [jacobiSym.sq_one]))
    (add norm 0 (by grind only [Nat.exists_coprime]))
    (add norm 0 (by grind only [ZMod.eq_zero_of_gcd_ne_one]))
    (add unsafe 10% (by grind only [Nat.pos_of_ne_zero]))
    (add unsafe 10% (by grind only [pos_of_gt]))
