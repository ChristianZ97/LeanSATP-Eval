
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

theorem aime_1983_p2 (p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15)
    (h₂ : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : IsLeast (f '' Set.Icc p 15) 15 := by
  have hp₁ := h₀.1
  simp [IsLeast, lowerBounds, IsMin]
  constructor <;> aesop
  ·
    refine
      ⟨15, ⟨by linarith, by linarith⟩, by
        rw [abs_of_pos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] <;> linarith⟩

  ·
    cases' abs_cases (x - p) with h h <;> cases' abs_cases (x - 15) with h' h' <;>
        cases' abs_cases (x - p - 15) with h'' h'' <;>

      linarith