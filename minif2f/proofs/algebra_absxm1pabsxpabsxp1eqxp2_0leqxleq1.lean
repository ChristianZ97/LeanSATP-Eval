
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

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  -- Step 1: Analyze case x < 0
  have h_neg_impossible : ¬(x < 0) := by
    intro hneg
    have h1 : x < 0 := hneg
    have h2 : abs x = -x := by rw [abs_of_neg h1]
    have h3 : x - 1 < 0 := by linarith
    have h4 : abs (x - 1) = -(x - 1) := by rw [abs_of_neg h3]
    cases abs_cases (x + 1) <;> linarith

  -- Step 2: Since x cannot be negative, x must be non-negative
  have h_nonneg : 0 ≤ x := by
    by_contra h
    have h1 : x < 0 := by linarith
    have h2 : ¬(x < 0) := h_neg_impossible
    exact h2 h1

  -- Step 3: Analyze upper bound
  have h_upper_bound : x ≤ 1 := by
    have h1 : 0 ≤ x := h_nonneg
    have h2 : abs x = x := by rw [abs_of_nonneg h1]
    have h3 : x + 1 ≥ 0 := by linarith
    have h4 : abs (x + 1) = x + 1 := by rw [abs_of_nonneg h3]
    have h5 : abs (x - 1) + x + (x + 1) = x + 2 := by
      rw [h2, h4] at h₀
      exact h₀

    have h6 : abs (x - 1) + 2 * x + 1 = x + 2 := by linarith
    have h7 : abs (x - 1) + x = 1 := by linarith
    have h8 : abs (x - 1) = 1 - x := by linarith
    have h9 : 1 - x ≥ 0 := by
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 600
        maxNormIterations := 320
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by positivity))
        (add norm 0 (by omega))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 0 (by gcongr))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [div_le_one']))
        (add norm 0 (by grind only [one_le_div']))
        (add norm 0 (by grind only [div_le_iff_le_mul]))
        (add norm 0 (by grind only [sub_one_lt]))
        (add norm 0 (by grind only [mul_le_mul_iff_right]))
        (add norm 0 (by grind only [le_div_iff_mul_le]))
        (add norm 0 (by grind only [abs_eq_self]))
        (add norm 0 (by grind only [abs_le]))
        (add norm 0 (by grind only [mabs_of_le_one]))
        (add norm 0 (by grind only [Real.dist_eq]))
        (add norm 0 (by grind only [le_mul_iff_one_le_left']))
        (add norm 0 (by grind only [div_le_self_iff]))
        (add norm 0 (by grind only [inv_div]))
        (add norm 0 (by grind only [mabs_div_comm]))
        (add norm 0 (by grind only [le_mul_iff_one_le_right']))
        (add norm 0 (by grind only [div_nonneg_iff]))
        (add norm 0 (by grind only [div_le_iff_le_mul']))
        (add norm 0 (by grind only [sub_half]))
        (add norm 0 (by grind only [mabs_of_one_le]))
        (add norm 0 (by grind only [le_of_lt]))
        (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq]))
        (add norm 0 (by grind only [Real.dist_le_of_mem_Icc]))
        (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul]))
        (add norm 0 (by grind only [mabs_lt]))
        (add norm 0 (by grind only [inv_le_inv_iff]))
        (add norm 0 (by grind only [tsub_le_iff_right]))
        (add norm 0 (by grind only [sub_eq_add]))
        (add norm 0 (by grind only [le_iff_eq_or_lt]))
        (add norm 0 (by grind only [mabs_of_lt_one]))
        (add norm 0 (by grind only [Real.two_le_pi]))
        (add unsafe 10% (by grind only [le_or_lt]))
        (add unsafe 10% (by grind only [le_total]))

    -- From abs(x-1) = 1-x, we know that x-1 must be <= 0 for the definition of abs to hold as such (or rather, if x > 1, abs(x-1) = x-1, so x-1 = 1-x => 2x=2 => x=1. If x<=1, abs(x-1)=1-x, so 1-x=1-x always true).
    -- Let's check if x > 1 leads to contradiction or specific value.
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [le_mul_iff_one_le_left']))
      (add norm 0 (by grind only [div_le_one']))
      (add norm 0 (by grind only [le_mul_iff_one_le_right']))
      (add norm 0 (by grind only [le_mul_of_one_le_right']))
      (add norm 0 (by grind only [one_le_div']))
      (add norm 0 (by grind only [div_le_self_iff]))
      (add norm 0 (by grind only [one_le_leOnePart]))
      (add norm 0 (by grind only [sq_le]))
      (add norm 0 (by grind only [zero_le_one]))
      (add norm 0 (by grind only [Int.le_add_one]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [abs_le]))
      (add norm 0 (by grind only [Real.exp_le_one_iff]))
      (add norm 0 (by grind only [one_le_oneLePart]))
      (add norm 0 (by grind only [one_le_sq_iff_one_le_abs]))
      (add norm 0 (by grind only [Real.log_nonpos]))
      (add norm 0 (by grind only [unitInterval.le_one]))
      (add norm 0 (by grind only [Real.two_le_pi]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [abs_eq_self]))
      (add norm 0 (by grind only [Real.log_nonneg]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 10% (by grind only [le_of_lt]))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 50% (by nlinarith [Int.cast_one_le_of_pos]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r_lower_bound_on_verticalStrip]))
      (add unsafe 50% (by nlinarith [le_mul_of_le_of_one_le]))
      (add unsafe 50% (by nlinarith [Real.logb_nonpos]))
      (add unsafe 50% (by nlinarith [one_le_mul_of_one_le_of_one_le]))

  -- Step 4: Combine results
  have h_final : 0 ≤ x ∧ x ≤ 1 := by
    exact ⟨h_nonneg, h_upper_bound⟩

  exact h_final
