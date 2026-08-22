
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

theorem amc12_2000_p12 :
    IsGreatest
      {(a*m*c + a*m + m*c + a*c) | (a : ℕ) (m : ℕ) (c : ℕ) (h₀ : a + m + c = 12)}
      112 := by
  -- Step 1: Define the expression E
  let E (a m c : ℕ) : ℕ := a*m*c + a*m + m*c + a*c
  -- Step 2 & 3: Show that E + a + m + c + 1 = (a+1)*(m+1)*(c+1)
  have h_factorization : ∀ (a m c : ℕ),
    (E a m c : ℤ) + ↑a + ↑m + ↑c + 1 = (↑a + 1) * (↑m + 1) * (↑c + 1) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
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
      (add norm 100 (by simp))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.cast_add]))
      (add norm 0 (by grind only [forall_const]))
      (add norm 0 (by rw [Int.ofNat_add]))
      (add norm 0 (by grind only [Nat.cast_succ]))
      (add norm 0 (by grind only [Nat.cast_mul]))
      (add norm 0 (by grind only [forall_true_iff]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [imp_true_iff]))
      (add norm 0 (by rw [Nat.cast_one]))
      (add norm 0 (by grind only [Num.cast_succ]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [eq_self_iff_true]))
      (add norm 0 (by rw [Zsqrtd.natCast_val]))
      (add norm 0 (by grind only [implies_true]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by rw [QuaternionAlgebra.coe_natCast]))
      (add norm 0 (by grind only [QuaternionGroup.a_mul_a]))
      (add norm 0 (by grind only [funext]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by rw [Nat.cast]))
      (add norm 0 (by grind only [Nat.factorial_succ]))
      (add norm 0 (by grind only [Eq.trans]))
      (add norm 0 (by grind only [true_and]))
      (add norm 0 (by grind only [Nat.succ_eq_add_one]))
      (add norm 0 (by grind only [true_and_iff]))
      (add norm 0 (by grind only [Nat.cast_add_choose]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [Pell.xz]))
      (add norm 0 (by grind only [Nat.cast_sub]))
      (add norm 0 (by grind only [Nat]))
      (add norm 0 (by grind only [Eq.symm]))
      (add norm 0 (by grind only [forall₂_true_iff]))

  -- Step 4: Given constraint a + m + c = 12
  -- This is part of the set definition, we use it locally when needed
  -- Step 5: Substitute a + m + c = 12 into the factorization
  -- If a + m + c = 12, then E + 13 = (a+1)(m+1)(c+1)
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    exists 4, 4, 4
  · rintro x ⟨a, m, c, h, r⟩
    have := h
    classical
    have : a ≤ 12 := by omega
    have : m ≤ 12 := by omega
    have : c ≤ 12 := by omega
    interval_cases a <;> interval_cases m <;> omega
