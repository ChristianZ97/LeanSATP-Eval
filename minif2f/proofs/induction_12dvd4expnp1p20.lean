
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

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  -- Base case check helper: 4^(0+1) + 20 = 24
  have h_base_val : (4 : ℤ) ^ (0 + 1) + 20 = 24 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [one_mul]))
      (add norm 0 (by grind only [pow_zero]))
      (add norm 0 (by grind only [pow_one]))
      (add norm 0 (by rw [mul_one]))
      (add norm 0 (by grind only [npow_zero]))
      (add norm 0 (by grind only [Nat.factorial_zero]))
      (add norm 0 (by grind only [Nat.pow_zero]))
      (add norm 0 (by grind only [MvPolynomial.C_1]))
      (add norm 0 (by grind only [LucasLehmer.X.ω]))
      (add norm 0 (by rw [one_pow]))
      (add norm 0 (by grind only [Finset.range_one]))
      (add norm 0 (by grind only [Nat.zero_eq]))
      (add norm 0 (by grind only [ArithmeticFunction.vonMangoldt_apply_one]))
      (add norm 0 (by grind only [MvPolynomial.esymm_zero]))
      (add norm 0 (by grind only [Nat.one_eq_succ_zero]))
      (add norm 0 (by grind only [tsub_zero]))
      (add norm 0 (by grind only [Fin.val_one]))
      (add norm 0 (by rw [jacobiSym.one_left]))
      (add norm 0 (by grind only [Polynomial.expand_one]))
      (add norm 0 (by grind only [geom_sum₂_with_one]))
      (add norm 0 (by grind only [DiscreteValuationRing.addVal_uniformizer]))
      (add norm 0 (by grind only [Nat.pow_one]))
      (add norm 0 (by grind only [Surreal.powHalf_zero]))
      (add norm 0 (by grind only [ppow_one]))
      (add norm 0 (by grind only [ArithmeticFunction.moebius_apply_one]))
      (add norm 0 (by grind only [Polynomial.hermite_zero]))
      (add norm 0 (by grind only [AlgebraicTopology.DoldKan.P_zero]))
      (add norm 0 (by rw [mul_self]))
      (add norm 0 (by grind only [Nat.centralBinom_zero]))
      (add norm 0 (by grind only [tsub_self]))
      (add norm 0 (by grind only [PerfectClosure.one_def]))
      (add norm 0 (by grind only [LucasLehmer.X.ωb]))

  -- 24 is divisible by 12
  induction n <;> simp [pow_succ, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  any_goals simp [Nat.pow_mod] <;> omega
