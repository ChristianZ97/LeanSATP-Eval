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


theorem mathd_algebra_188 (σ : ℝ ≃ ℝ) (h : σ 2 = σ.symm 2) : σ (σ 2) = 2 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 100 (by exfalso))
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
    (add norm 0 (by grind only [Equiv.apply_symm_apply]))
    (add norm 0 (by grind only [Equiv.symm_apply_apply]))
    (add norm 0 (by grind only [Equiv.eq_symm_apply]))
    (add norm 0 (by grind only [Eq.symm]))
    (add norm 0 (by grind only [FirstOrder.Language.Equiv.comp_apply]))
    (add norm 0 (by grind only [FirstOrder.Language.Equiv.symm_apply_apply]))
    (add norm 0 (by grind only [congrArg]))
    (add norm 0 (by grind only [Equiv]))
    (add norm 0 (by grind only [FirstOrder.Language.Equiv.apply_symm_apply]))
    (add norm 0 (by grind only [Homeomorph.symm_apply_apply]))
    (add norm 0 (by grind only [Equiv.symm_apply_eq]))
    (add norm 0 (by grind only [Eq.trans]))
    (add norm 0 (by grind only [CategoryTheory.ActionCategory.objEquiv]))
    (add norm 0 (by grind only [Equiv.coe_fn_symm_mk]))
    (add norm 0 (by grind only [circleEquivGen]))
    (add norm 0 (by grind only [unitInterval.symm_symm]))
    (add norm 0 (by grind only [IsPerfectClosure.equiv_symm]))
    (add norm 0 (by grind only [PEquiv.symm]))
    (add norm 0 (by grind only [IsPerfectClosure.equiv_symm_apply]))
    (add norm 0 (by grind only [SSet.horn.face]))
    (add norm 0 (by grind only [equivShrink]))
    (add norm 0 (by grind only [Equiv.injective]))
    (add norm 0 (by grind only [CategoryTheory.Iso.toEquiv_symm_fun]))
    (add norm 0 (by grind only [congrFun]))
    (add norm 0 (by grind only [unitInterval.symm]))
    (add norm 0 (by grind only [ContinuousLinearEquiv.apply_symm_apply]))
    (add norm 0 (by grind only [AlgebraCat.adj]))
    (add norm 0 (by grind only [FirstOrder.Language.Equiv.symm]))
    (add norm 0 (by grind only [CategoryTheory.Iso.toEquiv_fun]))
    (add norm 0 (by grind only [Polynomial.Gal.rootsEquivRoots]))
    (add norm 0 (by grind only [FirstOrder.Language.Formula.realize_equivSentence_symm_con]))
    (add norm 0 (by grind only [Ctop.Realizer.ofEquiv_F]))
