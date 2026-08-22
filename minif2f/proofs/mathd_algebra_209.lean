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


theorem mathd_algebra_209 (σ : ℝ ≃ ℝ) (h₀ : σ.symm 2 = 10) (h₁ : σ.symm 10 = 1)
    (h₂ : σ.symm 1 = 2) : σ (σ 10) = 1 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 0 (by push_neg))
    (add safe 100 (by interval_cases))
    (add safe 0 (by ext))
    (add safe 0 (by split))
    (add safe 0 (by exfalso))
    (add safe 1 (by ring_nf at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Equiv.apply_symm_apply]))
    (add norm 0 (by grind only [Eq.symm]))
    (add norm 0 (by grind only [Eq.trans]))
    (add norm 0 (by grind only [Equiv.symm_apply_apply]))
    (add norm 0 (by grind only [congrArg]))
    (add norm 0 (by grind only [IsPerfectClosure.equiv_symm]))
    (add norm 0 (by grind only [IsPerfectClosure.equiv_symm_apply]))
    (add norm 0 (by grind only [unitInterval.symm_symm]))
    (add norm 0 (by grind only [one_ne_zero]))
    (add norm 0 (by grind only [Equiv.one_def]))
    (add norm 0 (by grind only [symm]))
    (add norm 0 (by grind only [Equiv.eq_symm_apply]))
    (add norm 0 (by grind only [RingEquiv.apply_symm_apply]))
    (add norm 0 (by grind only [ModularCyclotomicCharacter.toFun_unique]))
    (add norm 0 (by grind only [GradedTensorProduct.of_symm_one]))
    (add norm 0 (by grind only [Equiv.coe_fn_symm_mk]))
    (add norm 0 (by grind only [unitInterval.coe_symm_eq]))
    (add norm 0 (by grind only [unitInterval.symm]))
    (add norm 0 (by grind only [IsPerfectClosure.equiv_apply]))
    (add norm 0 (by grind only [ModularCyclotomicCharacter.toFun_unique']))
    (add norm 0 (by grind only [congrFun]))
    (add norm 0 (by grind only [Grp.SurjectiveOfEpiAuxs.τ_symm_apply_infinity]))
    (add norm 0 (by grind only [Polynomial.Gal.rootsEquivRoots]))
    (add norm 0 (by grind only [FirstOrder.Language.Equiv.comp_apply]))
    (add norm 0 (by grind only [Equiv.coe_fn_mk]))
    (add norm 0 (by grind only [IsPerfectClosure.equiv_comp_equiv_apply_eq_self]))
    (add norm 0 (by grind only [AlgebraCat.coe_comp]))
    (add norm 0 (by grind only [RingNorm.apply_one]))
    (add norm 0 (by grind only [Ctop.Realizer.ofEquiv_F]))
    (add norm 0 (by grind only [IsPerfectClosure.equiv_comp_apply]))
    (add norm 0 (by grind only [Subtype.ext]))
    (add norm 0 (by grind only [Unitization.snd_one]))
