
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

theorem mathd_numbertheory_435 (k : ℕ) (h₀ : 0 < k) (h₁ : ∀ n, gcd (6 * n + k) (6 * n + 3) = 1)
    (h₂ : ∀ n, gcd (6 * n + k) (6 * n + 2) = 1) (h₃ : ∀ n, gcd (6 * n + k) (6 * n + 1) = 1) :
    5 ≤ k := by
  -- Step 1: gcd(k, 2) = 1
  have h_step1 : Nat.gcd k 2 = 1 := by
    clear * - h₂
    have tmp := h₂ 0
    simp at tmp <;> exact tmp

  -- Step 2: k = 2m + 1 (k is odd)
  have h_step2 : Odd k := by
    clear * - h_step1
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
      (add safe 100 (by positivity))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 1 (by ring_nf at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [ZMod.eq_zero_iff_even]))
      (add norm 0 (by grind only [Odd]))
      (add norm 0 (by grind only [Nat.odd_iff_not_even]))
      (add norm 0 (by grind only [Stream'.get_odd]))
      (add norm 0 (by grind only [IsSquare]))
      (add norm 0 (by rw [ZNum.gcd_to_nat]))
      (add unsafe 10% (by grind only [even_iff_two_dvd]))
      (add unsafe 50% (by nlinarith [Nat.odd_iff]))
      (add unsafe 10% (by grind only [jacobiSym.at_two]))
      (add unsafe 50% (by nlinarith [Nat.even_or_odd]))
      (add unsafe 10% (by grind only [irrational_sqrt_of_multiplicity_odd]))
      (add unsafe 10% (by grind only [FiniteField.odd_card_of_char_ne_two]))
      (add unsafe 50% (by nlinarith [Int.emod_eq_zero_of_dvd]))
      (add unsafe 50% (by nlinarith [Nat.even_iff]))
      (add unsafe 50% (by nlinarith [Nat.even_pow]))
      (add unsafe 50% (by nlinarith [Nat.odd_of_mod_four_eq_three]))
      (add unsafe 50% (by nlinarith [jacobiSym.quadratic_reciprocity_one_mod_four']))
      (add unsafe 50% (by nlinarith [jacobiSym.quadratic_reciprocity_one_mod_four]))
      (add unsafe 50% (by nlinarith [Nat.even_mul]))
      (add unsafe 10% (by grind only [FiniteField.even_card_iff_char_two]))
      (add unsafe 50% (by nlinarith [Nat.not_odd_iff]))
      (add unsafe 10% (by grind only [Nat.sum_four_squares_of_two_mul_sum_four_squares]))
      (add unsafe 50% (by rw [← Int.natCast_inj] at *))
      (add unsafe 50% (by nlinarith [Nat.not_even_iff]))
      (add unsafe 50% (by nlinarith [jacobiSym.quadratic_reciprocity_three_mod_four]))
      (add unsafe 50% (by nlinarith [Nat.dvd_iff_mod_eq_zero]))
      (add unsafe 10% (by grind only [FiniteField.even_card_of_char_two]))
      (add unsafe 50% (by nlinarith [Int.even_iff]))
      (add unsafe 10% (by grind only [exists_eq_mul_left_of_dvd]))
      (add unsafe 50% (by nlinarith [Nat.mod_mod_of_dvd]))
      (add unsafe 50% (by nlinarith [coprime_sq_sub_sq_sum_of_odd_odd]))
      (add unsafe 50% (by nlinarith [jacobiSym.mod_right']))

  -- Step 3: gcd(k, 3) = 1
  have h_step3 : Nat.gcd k 3 = 1 := by
    clear * - h₁
    have a := h₁ 0
    simp at a <;> apply Nat.Coprime.gcd_eq_one <;> aesop

  -- Step 4: k ≢ 0 (mod 3)
  have h_step4 : ¬(k % 3 = 0) := by
    clear * - h_step3
    revert h_step3
    simp [Nat.gcd_eq_iff]
    intro h₀ h₁
    have := h₀ 3 <;> simp_all [Nat.dvd_iff_mod_eq_zero]

  -- Step 5: k ≡ 1 (mod 6) ∨ k ≡ 5 (mod 6)
  have h_step5 : k % 6 = 1 ∨ k % 6 = 5 := by
    clear * - h_step2 h_step4
    cases' h_step2 with w h_step2
    subst h_step2 <;> omega

  -- Step 6: Assume k < 5, derive contradiction
  -- The possible values for k are 1, 2, 3, 4.
  -- From h_step5, k % 6 is 1 or 5.
  -- If k < 5, k can only be 1 (since 5 is not < 5).
  -- Let's show that if k=1, we get a contradiction.
  -- Case analysis on k < 5
  have h_step6_contradiction : ¬(k < 5) := by
    intro h_k_lt_5
    -- Since k > 0 and k < 5, k ∈ {1, 2, 3, 4}
    -- We know k is odd (h_step2), so k ∈ {1, 3}
    -- We know k % 3 ≠ 0 (h_step4), so k ≠ 3.
    -- Thus k = 1.
    interval_cases k <;> simp_all <;> contradiction

  -- Step 12 & 13: k ≥ 5
  have h_step_final : 5 ≤ k := by
    by_contra h_le
    push_neg at h_le
    -- h_le means k < 5
    exact h_step6_contradiction h_le

  exact h_step_final
