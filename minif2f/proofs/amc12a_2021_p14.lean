
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

theorem amc12a_2021_p14 :
    (∑ k ∈ Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) *
        ∑ k ∈ Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k) =

      21000 := by
  have h_sum1 : ∑ k ∈ Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2) = 210 * Real.logb 5 3 := by
    have h₀ : (0 : ℝ) < 5 := by norm_num
    norm_num [Real.logb, Finset.sum_Icc_succ_top]
    field_simp <;> norm_num <;> ring

  have h_sum2 : ∑ k ∈ Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k) = 100 * Real.logb 3 5 := by
    have h_sum2_expand : ∑ k ∈ Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k) = ∑ k ∈ Finset.Icc 1 100, Real.logb 9 25 := by
      apply Finset.sum_congr rfl
      intro k hk
      have h_base_pos : (0:ℝ) < 9 := by norm_num
      have h_arg_pos : (0:ℝ) < 25 := by norm_num
      have h_log_prop : Real.logb (9 ^ k) (25 ^ k) = Real.logb 9 25 := by
        rw [Real.logb]
        simp only [Real.log_pow, Real.log_div, ← mul_assoc]
        simp [← div_eq_mul_inv, Real.logb, h_base_pos, h_arg_pos]
        cases k <;> field_simp <;> norm_cast

      rw [h_log_prop]

    rw [h_sum2_expand]
    have h_const_sum : ∑ k ∈ Finset.Icc 1 100, Real.logb 9 25 = 100 * Real.logb 9 25 := by
      simp [Finset.sum_const]

    rw [h_const_sum]
    have h_log_conv : Real.logb 9 25 = Real.logb 3 5 := by
      rw [Real.logb]
      have h9 : Real.log 9 = 2 * Real.log 3 := by
        rw [← Real.log_rpow (by norm_num)] <;> norm_num

      have h25 : Real.log 25 = 2 * Real.log 5 := by
        rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow] <;> norm_num

      rw [h9, h25]
      simp [Real.logb, mul_comm, mul_div_mul_left]

    rw [h_log_conv]

  rw [h_sum1, h_sum2, mul_comm] <;> norm_num
  symm <;> norm_num [Real.logb, Real.log_div, mul_comm, mul_assoc, mul_left_comm]