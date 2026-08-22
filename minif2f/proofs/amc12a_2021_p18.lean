
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

theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f ((25 : ℚ) / 11) < 0 := by
  -- Step 1-3: Prove f(1) = 0
  have h_f1_eq_0 : f 1 = 0 := by
    have h_step1 : 1 = 1 * 1 := by norm_num
    have h_step2 : f (1 * 1) = f 1 + f 1 := by
      apply h₀
      <;> norm_num

    have h_step3 : f 1 = f 1 + f 1 := by
      aesop (config := {
        maxRuleApplications := 40
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        maxGoals := 256
        enableSimp := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 1 (by ext))
        (add norm 100 (by simp_all))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by interval_cases))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by rw [mul_one]))
        (add norm 0 (by rw [one_mul]))
        (add norm 0 (by rw [mul_self]))
        (add norm 0 (by grind only [Eq.symm]))
        (add norm 0 (by grind only [add_self]))
        (add norm 0 (by grind only [Eq.trans]))
        (add norm 0 (by grind only [AddChar.one_apply]))
        (add norm 0 (by grind only [mul_assoc]))
        (add norm 0 (by grind only [mul_right_inj]))
        (add norm 0 (by grind only [Nat.one_add]))
        (add norm 0 (by grind only [DualNumber.snd_eps]))
        (add norm 0 (by grind only [FractionalIdeal.dual_eq_mul_inv]))
        (add norm 0 (by grind only [mul_comm]))
        (add norm 0 (by grind only [mul_lt_mul_iff_left]))
        (add norm 0 (by grind only [LaurentPolynomial.T_zero]))
        (add norm 0 (by grind only [vsub_left_cancel]))
        (add norm 0 (by rw [Nat.cast_one]))
        (add norm 0 (by grind only [mul_left_inj]))
        (add norm 0 (by grind only [IsLprojection.mul_compl_self]))
        (add norm 0 (by rw [mul_le_mul_iff_left]))
        (add norm 0 (by grind only [add_idem]))
        (add norm 0 (by grind only [IsLprojection.distrib_lattice_lemma]))
        (add norm 0 (by grind only [Zsqrtd.not_divides_sq]))
        (add norm 0 (by grind only [Nat.mul_one]))
        (add norm 0 (by grind only [tsub_zero]))
        (add norm 0 (by grind only [self_eq_mul_left]))
        (add norm 0 (by grind only [BooleanRing.le_sup_inf_aux]))
        (add norm 0 (by grind only [HahnSeries.C_one]))
        (add norm 0 (by grind only [groupCohomology.map_one_fst_of_isMulTwoCocycle]))
        (add norm 0 (by grind only [LinearPMap.sup_apply]))
        (add norm 0 (by grind only [add_tsub_cancel_left]))
        (add norm 0 (by grind only [FractionalIdeal.count_self]))

    have h_step4 : f 1 = 0 := by
      linarith

    exact h_step4

  -- Step 5-8: Prove f(1/11) = -f(11)
  have h_f_inv11 : f (1 / 11) = - f 11 := by
    have h_step5 : f (11 * (1 / 11)) = f 11 + f (1 / 11) := by
      apply h₀
      <;> norm_num

    have h_step6 : f 1 = f 11 + f (1 / 11) := by
      have h_tmp : (11 : ℚ) * (1 / 11) = 1 := by norm_num
      rw [h_tmp] at h_step5
      exact h_step5

    have h_step7 : 0 = f 11 + f (1 / 11) := by
      rw [h_f1_eq_0] at h_step6
      exact h_step6

    have h_step8 : f (1 / 11) = - f 11 := by
      linarith

    exact h_step8

  -- Step 9-11: Express f(25/11) in terms of f(25) and f(1/11)
  have h_f_25_over_11_decomp : f ((25 : ℚ) / 11) = f 25 + f (1 / 11) := by
    have h_step9 : (25 : ℚ) / 11 = 25 * (1 / 11) := by norm_num
    rw [h_step9]
    have h_step10 : f (25 * (1 / 11)) = f 25 + f (1 / 11) := by
      apply h₀
      <;> norm_num

    exact h_step10

  -- Combine to get f(25/11) = f(25) - f(11)
  have h_f_25_over_11_sub : f ((25 : ℚ) / 11) = f 25 - f 11 := by
    rw [h_f_25_over_11_decomp]
    rw [h_f_inv11]
    ring
    <;> simp_all

  -- Step 12-17: Calculate f(25) = 10
  have h_f25_eq_10 : f 25 = 10 := by
    have h_step12 : (25 : ℚ) = 5 * 5 := by norm_num
    have h_step13 : f (5 * 5) = f 5 + f 5 := by
      apply h₀
      <;> norm_num

    have h_step14 : f 25 = f 5 + f 5 := by
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        maxGoals := 512
        enableSimp := false
        useDefaultSimpSet := false
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
        (add safe 0 (by exfalso))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Eq.symm]))
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [Eq.trans]))
        (add norm 0 (by grind only [mul_two]))
        (add norm 0 (by grind only [eq_div_iff_mul_eq']))
        (add norm 0 (by grind only [two_ne_zero']))
        (add norm 0 (by grind only [Ring.multichoose_two]))
        (add norm 0 (by grind only [Quaternion.star_add_self]))
        (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
        (add norm 0 (by grind only [eq_div_iff_mul_eq]))
        (add norm 0 (by grind only [Quaternion.self_add_star]))
        (add norm 0 (by grind only [mul_comm]))
        (add norm 0 (by grind only [Real.two_mul_arctan]))
        (add norm 0 (by grind only [groupCohomology.mem_twoCocycles_iff]))
        (add norm 0 (by grind only [div_eq_iff_eq_mul']))
        (add norm 0 (by grind only [Real.sin_two_mul]))
        (add norm 0 (by grind only [Quaternion.star_add_self']))
        (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
        (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
        (add norm 0 (by grind only [one_add_one_eq_two]))
        (add norm 0 (by grind only [Polynomial.natTrailingDegree_mul_mirror]))
        (add norm 0 (by grind only [ack_two]))
        (add norm 0 (by grind only [gosperCatalan]))
        (add norm 0 (by grind only [Complex.sin_two_mul]))
        (add norm 0 (by grind only [toIocMod_eq_iff]))
        (add norm 0 (by grind only [Polynomial.natDegree_mul_mirror]))
        (add norm 0 (by grind only [Int.cast_two]))
        (add norm 0 (by grind only [groupCohomology.mem_twoCocycles_def]))
        (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
        (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
        (add norm 0 (by grind only [Quaternion.self_add_star']))
        (add safe 1 (by simp_all only [div_eq_iff_eq_mul]))

    have h_step15 : f 5 = (5 : ℝ) := by
      have h_prime : Nat.Prime 5 := by decide
      have h_val : f 5 = (5 : ℝ) := by
        apply h₁
        exact h_prime

      exact h_val

    have h_step16 : f 5 + f 5 = (10 : ℝ) := by
      rw [h_step15]
      norm_num

    rw [h_step14]
    exact h_step16

  -- Step 18: Calculate f(11) = 11
  have h_f11_eq_11 : f 11 = 11 := by
    have h_prime : Nat.Prime 11 := by decide
    have h_val : f 11 = (11 : ℝ) := by
      apply h₁
      exact h_prime

    exact h_val

  -- Step 19-20: Calculate final value
  have h_final_val : f ((25 : ℚ) / 11) = -1 := by
    rw [h_f_25_over_11_sub]
    rw [h_f25_eq_10]
    rw [h_f11_eq_11]
    norm_num

  -- Step 21: Prove inequality
  have h_neg : f ((25 : ℚ) / 11) < 0 := by
    rw [h_final_val]
    norm_num

  exact h_neg
