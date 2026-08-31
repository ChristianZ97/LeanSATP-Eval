
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

theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  -- Step 1: Define g as the gcd of the two expressions
  let g := Nat.gcd (21 * n + 4) (14 * n + 3)
  -- Step 2 & 3 & 4: Use the property that gcd(a, b) = gcd(a - b, b)
  -- Specifically, gcd(21n+4, 14n+3) = gcd((21n+4) - (14n+3), 14n+3) = gcd(7n+1, 14n+3)
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (7 * n + 1) (14 * n + 3) := by
    clear * - h₀
    have h₁ : 21 * n + 4 = (7 * n + 1) + (14 * n + 3) := by ring
    simp [h₁, Nat.gcd_add_self_right]

  -- Step 5 & 6 & 7: Use the property that gcd(a, b) = gcd(a, b - k*a)
  -- Specifically, gcd(7n+1, 14n+3) = gcd(7n+1, (14n+3) - 2*(7n+1)) = gcd(7n+1, 1)
  have h2 : Nat.gcd (7 * n + 1) (14 * n + 3) = Nat.gcd (7 * n + 1) 1 := by
    clear * - h₀
    have : 14 * n + 3 = 2 * (7 * n + 1) + 1 := by ring
    simp [this, dvd_add, dvd_mul_right, Nat.gcd_assoc]

  -- Step 8: gcd(k, 1) = 1 for any natural number k
  have h3 : Nat.gcd (7 * n + 1) 1 = 1 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 16
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.gcd_comm]))
      (add norm 0 (by grind only [Nat.gcd_add_self_right]))
      (add norm 0 (by grind only [Nat.gcd_rec]))
      (add norm 0 (by grind only [Nat.gcd_one_left]))
      (add norm 0 (by grind only [PNat.one_gcd]))
      (add norm 0 (by grind only [gcd_eq_nat_gcd]))
      (add norm 0 (by rw [PNat.gcd_one]))
      (add norm 0 (by grind only [Nat.gcd_def]))
      (add norm 0 (by rw [Nat.fib_gcd]))
      (add norm 0 (by rw [Nat.gcd_fib_add_self]))
      (add norm 0 (by grind only [Nat.gcd_fib_add_mul_self]))
      (add norm 0 (by rw [Nat.coprime_iff_gcd_eq_one]))
      (add norm 0 (by rw [Num.gcd_to_nat]))
      (add norm 0 (by rw [PNat.gcd_comm]))
      (add norm 0 (by rw [ZNum.gcd_to_nat]))
      (add norm 0 (by rw [Int.gcd_eq_natAbs]))
      (add norm 0 (by rw [PNat.gcd_coe]))
      (add norm 0 (by grind only [ZMod.mul_inv_eq_gcd]))
      (add norm 0 (by rw [Nat.Coprime.gcd_eq_one]))
      (add norm 0 (by grind only [Nat.gcd]))
      (add norm 0 (by grind only [Nat.gcd_add_self_left]))
      (add norm 0 (by grind only [Nat.mul_one]))
      (add norm 0 (by grind only [Nat.gcd_succ]))
      (add norm 0 (by grind only [Nat.div_one]))
      (add norm 0 (by rw [Nat.gcd_eq_gcd_ab]))
      (add norm 0 (by rw [Int.gcd_eq_one_iff_coprime]))
      (add norm 0 (by rw [Num.gcd]))
      (add norm 0 (by grind only [Nat.gcd_add_mul_left_right]))
      (add norm 0 (by grind only [Nat.Coprime]))
      (add norm 0 (by rw [Num.gcd_to_nat_aux]))
      (add norm 0 (by rw [Int.gcd_natCast_natCast]))
      (add norm 0 (by grind only [Nat.coprime_of_squarefree_mul]))

  -- Combine all steps to conclude g = 1
  have h4 : g = 1 := by
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      maxGoals := 256
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
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
      (add norm 0 (by grind only [jacobiSym.sq_one']))
      (add norm 0 (by grind only [Nat.gcd_eq_gcd_ab]))
      (add norm 0 (by grind only [jacobiSym.sq_one]))
      (add norm 0 (by grind only [Int.gcd_eq_natAbs]))
      (add norm 0 (by grind only [Nat.gcd]))
      (add norm 0 (by grind only [PNat.gcd_coe]))
      (add norm 0 (by grind only [ZNum.gcd_to_nat]))
      (add norm 0 (by grind only [Num.gcd_to_nat]))
      (add norm 0 (by grind only [PNat.gcd]))
      (add norm 0 (by grind only [Int.gcd_eq_one_iff_coprime]))
      (add norm 0 (by grind only [PNat.gcd_comm]))
      (add norm 0 (by grind only [Nat.Coprime.gcd_eq_one]))
      (add norm 0 (by grind only [Nat.fib_gcd]))
      (add norm 0 (by grind only [ZMod.mul_inv_eq_gcd]))
      (add norm 0 (by grind only [Int.gcd_natCast_natCast]))
      (add norm 0 (by grind only [Nat.gcd_fib_add_mul_self]))
      (add norm 0 (by grind only [Int.gcd_comm]))
      (add norm 0 (by grind only [Nat.coprime_iff_gcd_eq_one]))
      (add norm 0 (by grind only [Num.gcd_to_nat_aux]))
      (add norm 0 (by grind only [Int.gcd_eq_gcd_ab]))
      (add norm 0 (by grind only [Num.gcd]))
      (add norm 0 (by grind only [Int.isCoprime_iff_gcd_eq_one]))
      (add norm 0 (by grind only [jacobiSym.eq_one_or_neg_one]))
      (add norm 0 (by grind only [Nat.gcd_comm]))
      (add norm 0 (by grind only [Int.gcd]))
      (add norm 0 (by grind only [Nat.gcd_def]))
      (add norm 0 (by grind only [gcd_eq_nat_gcd]))
      (add norm 0 (by grind only [jacobiSym.ne_zero]))
      (add norm 0 (by grind only [PNat.one_gcd]))
      (add norm 0 (by grind only [pow_gcd_eq_one]))
      (add norm 0 (by grind only [Int.coe_gcd]))
      (add norm 0 (by grind only [Nat.periodic_gcd]))

  exact h4
