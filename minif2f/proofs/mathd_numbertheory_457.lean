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


theorem mathd_numbertheory_457 : IsLeast {n : ℕ | 0 < n ∧ 80325 ∣ n !} 17 := by

  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    enableSimp := false
    enableUnfold := false
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
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 100 (by assumption_mod_cast))
    (add unsafe 50% (by grind only [ContinuousLinearMap.isLeast_opNorm]))
    (add unsafe 90% (by rw [← convexHull_toCone_isLeast] at *))
    (add unsafe 50% (by grind only [ContinuousMultilinearMap.isLeast_opNNNorm]))
    (add unsafe 50% (by grind only [ContinuousLinearMap.isLeast_opNNNorm]))
    (add unsafe 50% (by grind only [IsClosed.isLeast_csInf]))
    (add unsafe 90% (by rw [← Cardinal.not_isLimit_natCast] at *))
    (add unsafe 50% (by grind only [MonotoneOn.map_isLeast]))
    (add unsafe 90% (by rw [← Ordinal.opow_isLimit_left] at *))
    (add unsafe 50% (by grind only [IsLeast]))
    (add unsafe 90% (by rw [← Ordinal.isOpen_singleton_iff] at *))
    (add unsafe 90% (by rw [← Cardinal.IsLimit] at *))
    (add unsafe 90% (by rw [← CategoryTheory.Limits.limit.isLimitToOver] at *))
    (add unsafe 90% (by rw [← Ordinal.IsNormal.isLimit] at *))
    (add unsafe 50% (by grind only [ContinuousMultilinearMap.isLeast_opNorm]))
    (add unsafe 90% (by rw [← CategoryTheory.Limits.Multifork.IsLimit.lift] at *))
    (add unsafe 90% (by rw [← Ordinal.mul_isLimit] at *))
    (add unsafe 90% (by rw [← Ordinal.mul_isLimit_left] at *))
    (add unsafe 90% (by rw [← Ordinal.opow_isLimit] at *))
    (add unsafe 90% (by rw [← CategoryTheory.liftedLimitIsLimit] at *))
    (add unsafe 90% (by rw [← CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd] at *))
    (add unsafe 90% (by rw [← CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst] at *))
    (add unsafe 90% (by rw [← Ordinal.IsLimit] at *))
    (add unsafe 90% (by rw [← CategoryTheory.Limits.isLimitOfIsLimitFanMkObj] at *))
    (add unsafe 90% (by rw [← CategoryTheory.coyonedaJointlyReflectsLimits] at *))
    (add unsafe 90% (by rw [← TopCat.isSheaf_of_isLimit] at *))
    (add unsafe 90% (by rw [← CategoryTheory.Limits.Multifork.IsLimit.mk] at *))
    (add unsafe 90% (by rw [← CoxeterMatrix.IsLiftable] at *))
    (add unsafe 90% (by rw [← CategoryTheory.ShortComplex.isLimitOfIsLimitπ] at *))
    (add unsafe 90% (by rw [← CategoryTheory.Limits.KernelFork.IsLimit.ofId] at *))
    (add unsafe 90% (by rw [← CompHaus.pullback.isLimit] at *))
    (add unsafe 90% (by rw [← CategoryTheory.Limits.PullbackCone.IsLimit.lift'] at *))
    (add unsafe 90% (by rw [← CategoryTheory.Limits.Fork.isLimitOfIsos] at *))
