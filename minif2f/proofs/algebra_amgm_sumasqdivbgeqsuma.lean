
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

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩

  -- Step 1: a^2/b + b >= 2a
  have h1 : a^2 / b + b ≥ 2 * a := by
    clear * - ha hb
    field_simp
    nlinarith [sq_nonneg (a - b), sq_nonneg (-a + b)]

  -- Step 2: b^2/c + c >= 2b
  have h2 : b^2 / c + c ≥ 2 * b := by
    clear * - hb hc
    field_simp [sq]
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]

  -- Step 3: c^2/d + d >= 2c
  have h3 : c^2 / d + d ≥ 2 * c := by
    clear * - hc hd
    rw [two_mul]
    have hcd := mul_pos hc hd
    field_simp [sq, hcd.ne']
    nlinarith [sq_nonneg (c - d), hc, hd, hcd]

  -- Step 4: d^2/a + a >= 2d
  have h4 : d^2 / a + a ≥ 2 * d := by
    clear * - hd ha
    field_simp [ha.ne', hd.ne']
    nlinarith [sq_nonneg (d - a), mul_pos ha hd]

  -- Step 5: Summing up all inequalities
  have h5 : a^2 / b + b^2 / c + c^2 / d + d^2 / a + a + b + c + d ≥ 2 * a + 2 * b + 2 * c + 2 * d := by
    clear * - h1 h2 h3 h4
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_right]))
      (add norm 0 (by grind only [le_div_iff]))
      (add norm 0 (by grind only [mul_add_mul_le_mul_add_mul]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add norm 0 (by grind only [mul_mul_mul_comm]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [le_mul_tsub]))
      (add norm 0 (by grind only [mul_le_mul_right]))
      (add norm 0 (by grind only [div_le_iff]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [mul_self_le_mul_self]))
      (add norm 0 (by grind only [le_mul_left]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [div_le_iff']))
      (add norm 0 (by grind only [one_add_mul_le_pow]))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [Finset.mul_pluennecke_petridis]))
      (add safe 0 (by simp only [mul_div_assoc] at *))

  -- Step 6: Factor out 2 on RHS
  have h6 : 2 * a + 2 * b + 2 * c + 2 * d = 2 * (a + b + c + d) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      maxGoals := 512
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by push_cast))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [Quaternion.self_add_star]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [Quaternion.star_add_self]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [Quaternion.star_add_self']))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self]))
      (add norm 0 (by grind only [ack_two]))
      (add norm 0 (by grind only [Quaternion.self_add_star']))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_two]))
      (add norm 0 (by grind only [QuaternionAlgebra.self_add_star']))
      (add norm 0 (by grind only [one_add_one_eq_two]))
      (add norm 0 (by grind only [Nat.fib_two_mul_add_one]))
      (add norm 0 (by grind only [QuaternionAlgebra.star_add_self']))
      (add norm 0 (by grind only [Real.sin_two_mul]))
      (add norm 0 (by grind only [Real.two_mul_arctan_sub_pi]))
      (add norm 0 (by grind only [add_halves]))
      (add norm 0 (by grind only [Int.cast_two]))
      (add norm 0 (by grind only [Ring.multichoose_two]))
      (add norm 0 (by grind only [pow_two]))
      (add norm 0 (by grind only [Nat.two_mul]))
      (add norm 0 (by grind only [two_ne_zero']))
      (add norm 0 (by grind only [Int.sq_add_sq_of_two_mul_sq_add_sq]))
      (add norm 0 (by grind only [Finset.mulETransformLeft.card]))
      (add norm 0 (by grind only [Real.two_mul_arctan_add_pi]))
      (add norm 0 (by grind only [Real.two_mul_arctan]))

  -- Step 7: Substitute into inequality
  have h7 : a^2 / b + b^2 / c + c^2 / d + d^2 / a + a + b + c + d ≥ 2 * (a + b + c + d) := by
    clear * - h5 h6
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 320
      maxGoals := 16
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 1 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [mul_add_mul]))
      (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add norm 0 (by grind only [mul_add_mul_le_mul_add_mul]))
      (add norm 0 (by grind only [le_mul_left]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_right]))
      (add norm 0 (by grind only [le_trans]))
      (add norm 0 (by grind only [Real.BohrMollerup.f_add_nat_ge]))
      (add norm 0 (by grind only [le_mul_tsub]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [le_mul_of_one_le_right']))
      (add norm 0 (by grind only [le_mul_right]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [Surreal.double_powHalf_succ_eq_powHalf]))
      (add unsafe 50% (by nlinarith [Ordnode.ratio]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₅]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.merge_lemma]))

  -- Step 8: Subtract (a+b+c+d) from both sides to get final result
  have h8 : a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
    clear * - h7
    aesop (config := {
      maxRuleApplications := 100
      maxNormIterations := 320
      maxGoals := 16
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by rw [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 0 (by grind only [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [mul_le_mul_left]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [le_mul_left]))
      (add norm 0 (by grind only [Real.BohrMollerup.f_add_nat_ge]))
      (add norm 0 (by grind only [two_mul]))
      (add norm 0 (by grind only [mul_add_mul_le_mul_add_mul]))
      (add norm 0 (by grind only [mul_two]))
      (add norm 0 (by grind only [mul_right_comm]))
      (add norm 0 (by grind only [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add norm 0 (by grind only [le_trans]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_right]))
      (add norm 0 (by grind only [SzemerediRegularity.m_add_one_div_m_le_one_add]))
      (add norm 0 (by grind only [one_add_mul_le_pow]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [le_mul_of_one_le_right']))
      (add norm 0 (by grind only [le_mul_tsub]))
      (add norm 0 (by grind only [mul_left_comm]))
      (add norm 0 (by grind only [Valuation.map_add_le]))
      (add norm 0 (by grind only [le_mul_right]))
      (add norm 0 (by grind only [le_div_iff]))
      (add norm 0 (by grind only [Nat.le_add_left]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₅]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₄]))

  exact h8
