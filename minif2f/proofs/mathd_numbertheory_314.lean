
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

theorem mathd_numbertheory_314 (r : ℕ) (h₀ : r = 1342 % 13) :
    IsLeast {n : ℕ | 0 < n ∧ 1342 ∣ n ∧ n % 13 < r} 6710 := by
  -- Step 1 & 2 & 3: Calculate r = 1342 mod 13 = 3
  have h_r_val : r = 3 := by
    clear * - h₀
    aesop (config := {
      maxRuleApplications := 40
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
      (add norm 0 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.mod_two_add_succ_mod_two]))
      (add norm 0 (by grind only [Nat.add_mod_left]))
      (add norm 0 (by grind only [Nat.add_mod]))
      (add unsafe 10% (by grind only [Nat.mod_mod]))
      (add unsafe 10% (by grind only [Nat.mod_mod_of_dvd]))
      (add unsafe 10% (by grind only [Nat.mod_eq_zero_of_dvd]))
      (add unsafe 10% (by grind only [Nat.dvd_iff_mod_eq_zero]))
      (add unsafe 10% (by grind only [Nat.mul_mod]))
      (add unsafe 10% (by grind only [Nat.one_mod_of_ne_one]))
      (add unsafe 10% (by grind only [Nat.mod_mul_left_mod]))
      (add unsafe 10% (by grind only [neg_one_pow_eq_pow_mod_two]))
      (add unsafe 10% (by grind only [Num.dvd_iff_mod_eq_zero]))
      (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_one_mod_four]))
      (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_one_mod_four']))
      (add unsafe 10% (by grind only [Nat.pow_mod]))
      (add unsafe 10% (by grind only [Nat.odd_iff]))
      (add unsafe 50% (by nlinarith [Nat.mul_mod_left]))
      (add unsafe 10% (by grind only [Nat.ModEq]))
      (add unsafe 10% (by grind only [Nat.mod_mul_mod]))
      (add unsafe 10% (by grind only [Num.mod_to_nat]))
      (add unsafe 10% (by grind only [Nat.mul_mod_mod]))
      (add unsafe 10% (by grind only [Nat.gcd.induction]))
      (add unsafe 10% (by grind only [Nat.mod_two_ne_zero]))
      (add unsafe 50% (by nlinarith [Nat.mul_mod_mul_left]))
      (add unsafe 10% (by grind only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
      (add unsafe 10% (by grind only [PNat.mod_coe]))
      (add unsafe 10% (by grind only [Nat.zero_mod]))
      (add unsafe 50% (by nlinarith [ZMod.natCast_eq_natCast_iff']))
      (add unsafe 50% (by nlinarith [Nat.mul_mod_right]))
      (add unsafe 50% (by nlinarith [Nat.even_iff]))
      (add unsafe 10% (by grind only [Nat.ofDigits_mod]))
      (add unsafe 10% (by grind only [Nat.mod_two_ne_one]))

  -- Step 4: Define n_min candidate
  let n_min : ℕ := 6710
  -- Step 5: Verify that 1342 divides n_min
  have h_divides : 1342 ∣ n_min := by
    clear * -
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
      (add norm 1 (by ext))
      (add norm 100 (by ring_nf at *))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 100 (by ring_nf))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.dvd_trans]))
      (add norm 0 (by grind only [Nat.dvd_refl]))
      (add norm 0 (by grind only [dvd_trans]))
      (add norm 0 (by grind only [Nat.dvd_sub']))
      (add norm 0 (by grind only [Nat.Coprime.coprime_dvd_left]))
      (add norm 0 (by grind only [Nat.dvd_of_forall_prime_mul_dvd]))
      (add norm 0 (by grind only [Nat.dvd_iff_dvd_ofDigits]))
      (add norm 0 (by grind only [PNat.le_of_dvd]))
      (add norm 0 (by grind only [Function.IsPeriodicPt.minimalPeriod_dvd]))
      (add norm 0 (by grind only [Nat.dvd_div_iff_mul_dvd]))
      (add norm 0 (by grind only [Nat.dvd_iff_dvd_digits_sum]))
      (add norm 0 (by grind only [Nat.fib_dvd]))
      (add norm 0 (by grind only [orderOf_pow_dvd]))
      (add norm 0 (by grind only [ONote.NF.of_dvd_omega]))
      (add norm 0 (by grind only [Nat.totient_dvd_of_dvd]))
      (add norm 0 (by grind only [Finset.dvd_prod_of_mem]))
      (add norm 0 (by grind only [Nat.ord_proj_dvd_ord_proj_of_dvd]))
      (add norm 0 (by grind only [Nat.dvd_add_right]))
      (add norm 0 (by grind only [Nat.Coprime.mul_dvd_of_dvd_of_dvd]))
      (add norm 0 (by grind only [Nat.dvd_lcm_left]))
      (add norm 0 (by grind only [List.dvd_sum]))
      (add norm 0 (by grind only [Polynomial.eval_dvd]))
      (add norm 0 (by grind only [Nat.prodDvdAndDvdOfDvdProd]))
      (add norm 0 (by grind only [Pell.dvd_of_ysq_dvd]))
      (add norm 0 (by grind only [Monoid.exponent_dvd]))
      (add norm 0 (by grind only [Nat.lcm_dvd]))
      (add norm 0 (by grind only [Nat.minFac_dvd]))
      (add norm 0 (by grind only [Fintype.prod_dvd_of_coprime]))
      (add norm 0 (by grind only [ONote.NF.of_dvd_omega_opow]))
      (add norm 0 (by grind only [Finset.prod_dvd_prod_of_dvd]))
      (add unsafe 10% (by grind only [Nat.minSqFacProp_div]))
      (add unsafe 10% (by grind only [Pell.y_dvd_iff]))

  -- Step 6: Verify that n_min > 0
  have h_pos : 0 < n_min := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by norm_num))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 100 (by ring_nf))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.succ_pos']))
      (add unsafe 10% (by grind only [Nat.le_induction]))
      (add unsafe 10% (by grind only [Nat.zero_le]))
      (add unsafe 10% (by grind only [Nat.le_of_lt_succ]))
      (add unsafe 10% (by grind only [Nat.le_succ]))
      (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
      (add unsafe 10% (by grind only [lt_add_one]))
      (add unsafe 10% (by grind only [Nat.le_succ_of_le]))
      (add unsafe 10% (by grind only [Nat.succ_le_succ]))
      (add unsafe 10% (by grind only [Nat.lt_succ_of_le]))
      (add unsafe 10% (by grind only [Nat.sub_lt]))
      (add unsafe 10% (by grind only [Nat.succ_pos]))
      (add unsafe 10% (by grind only [Nat.lt_of_succ_le]))
      (add unsafe 10% (by grind only [Pell.x_pos]))
      (add unsafe 10% (by grind only [Nat.zero_lt_succ]))
      (add unsafe 10% (by grind only [Nat.div_lt_self]))
      (add unsafe 10% (by grind only [Nat.dist_pos_of_ne]))
      (add unsafe 10% (by grind only [one_lt_two]))
      (add unsafe 10% (by grind only [Nat.supOfSeq]))
      (add unsafe 10% (by grind only [CategoryTheory.IsCofiltered.CofilteredClosure]))
      (add unsafe 10% (by grind only [Finset.Ico_subset_Ico]))
      (add unsafe 10% (by grind only [PicardLindelof.tMin_le_tMax]))
      (add unsafe 10% (by grind only [Finset.Ico]))
      (add unsafe 10% (by grind only [lt_trans]))
      (add unsafe 10% (by grind only [Nat.pred_lt]))
      (add unsafe 10% (by grind only [Nat.lt_succ_self]))
      (add unsafe 10% (by grind only [Nat.eq_zero_or_pos]))
      (add unsafe 10% (by grind only [Nat.succ_le_iff]))
      (add unsafe 10% (by grind only [Nat.le_of_succ_le_succ]))
      (add unsafe 10% (by grind only [Pell.strictMono_y]))
      (add unsafe 10% (by grind only [Nat.zero_lt_of_lt]))
      (add unsafe 10% (by grind only [Pell.yn_ge_n]))

  -- Step 7: Calculate n_min mod 13. Since 1342 = 13*103 + 3, 1342 ≡ 3 mod 13.
  -- n_min = 1342 * 5, so n_min ≡ 3 * 5 ≡ 15 ≡ 2 mod 13.
  have h_mod_calc : n_min % 13 = 2 := by
    clear * - h_r_val
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
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 100 (by ring_nf))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 1 (by ring_nf at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.mod_add_div]))
      (add norm 0 (by grind only [Nat.add_mod]))
      (add norm 0 (by grind only [Nat.add_mod_left]))
      (add norm 0 (by grind only [Nat.mul_add_mod]))
      (add norm 0 (by grind only [Nat.div_add_mod]))
      (add norm 0 (by grind only [Nat.mod_mul_right_mod]))
      (add unsafe 10% (by grind only [Nat.mod_mod]))
      (add unsafe 10% (by grind only [Nat.mod_lt]))
      (add unsafe 10% (by grind only [Nat.mul_mod]))
      (add unsafe 10% (by grind only [Nat.mod_mul_left_mod]))
      (add unsafe 10% (by grind only [Nat.mod_mod_of_dvd]))
      (add unsafe 10% (by grind only [Num.mod_to_nat]))
      (add unsafe 10% (by grind only [Nat.dvd_iff_mod_eq_zero]))
      (add unsafe 10% (by grind only [Nat.ModEq]))
      (add unsafe 10% (by grind only [Nat.mod_eq_zero_of_dvd]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add unsafe 10% (by grind only [Nat.mod_two_add_succ_mod_two]))
      (add unsafe 10% (by grind only [Nat.mod_injOn_Ico]))
      (add unsafe 50% (by nlinarith [Nat.mul_mod_mul_left]))
      (add unsafe 10% (by grind only [Nat.mod_mul_mod]))
      (add unsafe 10% (by grind only [Num.dvd_iff_mod_eq_zero]))
      (add unsafe 10% (by grind only [neg_one_pow_eq_pow_mod_two]))
      (add unsafe 10% (by grind only [Nat.one_mod_of_ne_one]))
      (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_one_mod_four']))
      (add unsafe 10% (by grind only [Nat.odd_iff]))
      (add unsafe 10% (by grind only [Nat.gcd.induction]))
      (add unsafe 50% (by nlinarith [Nat.mul_mod_left]))
      (add unsafe 10% (by grind only [PNat.XgcdType.r]))
      (add unsafe 10% (by grind only [Nat.pow_mod]))
      (add unsafe 10% (by grind only [Nat.mul_mod_mod]))
      (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_one_mod_four]))
      (add unsafe 10% (by grind only [Nat.zero_mod]))

  -- Step 8: Check condition n_min % 13 < r. i.e., 2 < 3.
  have h_cond_satisfied : n_min % 13 < r := by
    clear * - h_mod_calc h_r_val
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
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by grind only [Nat.mod_lt]))
      (add unsafe 10% (by grind only [Pell.x_pos]))
      (add unsafe 10% (by grind only [Pell.d_pos]))
      (add unsafe 10% (by grind only [Pell.strictMono_x]))
      (add unsafe 10% (by grind only [Nat.mod_le]))
      (add unsafe 10% (by grind only [Pell.yn_ge_n]))
      (add unsafe 10% (by grind only [Ordnode.Valid'.rotateL_lemma₂]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem3]))
      (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
      (add unsafe 10% (by grind only [Pell.strictMono_y]))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
      (add unsafe 10% (by grind only [le_of_lt]))
      (add unsafe 10% (by grind only [lt_of_le_of_lt]))
      (add unsafe 10% (by grind only [Ordnode.Valid'.rotateL_lemma₃]))
      (add unsafe 10% (by grind only [Nat.zero_le]))
      (add unsafe 10% (by grind only [Pell.xn]))
      (add unsafe 10% (by grind only [Ordnode.Sized.pos]))
      (add unsafe 10% (by grind only [mul_lt_mul]))
      (add unsafe 10% (by grind only [Pell.n_lt_xn]))
      (add unsafe 10% (by grind only [lt_add_one]))
      (add unsafe 10% (by grind only [le_trans]))
      (add unsafe 10% (by grind only [Nat.succ_le_iff]))
      (add unsafe 10% (by grind only [Nat.le_succ_of_le]))
      (add unsafe 10% (by grind only [mul_lt_mul']))
      (add unsafe 10% (by grind only [lt_of_lt_of_le]))
      (add unsafe 10% (by grind only [Nat.le_succ]))
      (add unsafe 10% (by grind only [Nat.mul_div_lt_iff_not_dvd]))
      (add unsafe 10% (by grind only [Nat.le_add_left]))
      (add unsafe 10% (by grind only [Ordnode.ratio]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₁]))
      (add unsafe 10% (by grind only [Nat.lt_of_succ_le]))
      (add unsafe 10% (by grind only [lt_of_mul_lt_mul_right]))

  -- Step 9: Assemble that n_min is in the set
  have h_in_set : n_min ∈ {n : ℕ | 0 < n ∧ 1342 ∣ n ∧ n % 13 < r} := by
    clear * - h_pos h_divides h_cond_satisfied
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [gt_iff_lt]))
      (add norm 0 (by grind only [Nat.dvd_sub']))
      (add norm 0 (by grind only [Nat.Coprime.mul_dvd_of_dvd_of_dvd]))
      (add norm 0 (by grind only [dvd_of_mul_left_dvd]))
      (add norm 0 (by grind only [Nat.dvd_trans]))
      (add norm 0 (by grind only [Finset.dvd_prod_of_mem]))
      (add norm 0 (by grind only [Set.mem_setOf]))
      (add unsafe 10% (by grind only [dvd_trans]))
      (add unsafe 10% (by grind only [Pell.y_dvd_iff]))
      (add unsafe 10% (by grind only [Nat.le_of_dvd]))
      (add unsafe 10% (by grind only [Pell.yn_ge_n]))
      (add unsafe 10% (by grind only [Pell.dvd_of_ysq_dvd]))
      (add unsafe 10% (by grind only [Pell.strictMono_y]))
      (add unsafe 10% (by grind only [Nat.dvd_sub]))
      (add unsafe 10% (by grind only [Pell.yn_modEq_two]))
      (add unsafe 10% (by grind only [Nat.dvd_two_of_totient_le_one]))
      (add unsafe 10% (by grind only [Pell.yn_modEq_a_sub_one]))
      (add unsafe 10% (by grind only [Nat.mul_div_lt_iff_not_dvd]))
      (add unsafe 10% (by grind only [Nat.dvd_factorial]))
      (add unsafe 10% (by grind only [le_of_lt]))
      (add unsafe 10% (by grind only [ONote.NF.of_dvd_omega_opow]))
      (add unsafe 10% (by grind only [Pell.x_pos]))
      (add unsafe 10% (by grind only [Nat.not_dvd_of_between_consec_multiples]))
      (add unsafe 10% (by grind only [Nat.minSqFacProp_div]))
      (add unsafe 10% (by grind only [Pell.xn]))
      (add unsafe 10% (by grind only [lt_add_one]))
      (add unsafe 10% (by grind only [Pell.xy_modEq_of_modEq]))
      (add unsafe 10% (by grind only [lt_of_le_of_lt]))
      (add unsafe 10% (by grind only [Pell.d_pos]))
      (add unsafe 10% (by grind only [Pell.xy_coprime]))
      (add unsafe 10% (by grind only [PosNum.dvd_to_nat]))
      (add unsafe 10% (by grind only [Pell.strictMono_x]))

  -- Step 10: Now we need to prove minimality.
  -- Let m be any element in the set. We must show n_min ≤ m.
  -- intro m hm
  -- rcases hm with ⟨hm_pos, hm_div, hm_mod⟩
  -- From hm_div, m = 1342 * k for some k > 0 (since m > 0 and 1342 > 0)
  -- Actually, 1342 ∣ m implies ∃ k, m = 1342 * k.
  -- Since 0 < m, and 1342 > 0, we must have k > 0, so k ≥ 1.
  -- We know m % 13 < r = 3.
  -- Also m ≡ 1342 * k ≡ 3 * k (mod 13).
  -- So (3 * k) % 13 < 3.
  -- Let's verify the minimal k.
  -- k=1: 3*1=3. 3%13=3. Not < 3.
  -- k=2: 3*2=6. 6%13=6. Not < 3.
  -- k=3: 3*3=9. 9%13=9. Not < 3.
  -- k=4: 3*4=12. 12%13=12. Not < 3.
  -- k=5: 3*5=15. 15%13=2. 2 < 3. Valid.
  -- So the smallest positive integer k satisfying the condition is 5.
  -- Thus the smallest m is 1342 * 5 = 6710.
  -- Lemma: If 1342 ∣ m, then m = 1342 * (m / 1342).
  -- have h_m_form : m = 1342 * (m / 1342) := by
    -- prove_with[hm_div]

  -- let k := m / 1342
  -- Since 0 < m and 1342 > 0, k ≥ 1.
  -- have h_k_pos : 1 ≤ k := by
    -- prove_with[hm_pos, hm_div]

  -- The condition m % 13 < r becomes (1342 * k) % 13 < 3.
  -- Since 1342 % 13 = 3, this is (3 * k) % 13 < 3.
  -- have h_k_cond : (3 * k) % 13 < 3 := by
    -- prove_with[hm_mod, h_r_val]

  -- We need to show that if (3 * k) % 13 < 3 for k ≥ 1, then k ≥ 5.
  -- This implies m = 1342 * k ≥ 1342 * 5 = 6710 = n_min.
  -- Let's break down possible values of k modulo 13 or just check small k.
  -- Since we are in Nat, we can argue by cases on k being less than 5 or greater/equal.
  -- But simpler: Just establish that for k ∈ {1, 2, 3, 4}, the condition fails.
  -- Helper: For any k : ℕ, if k < 5 and k >= 1, then (3*k)%13 >= 3.
  -- k=1: 3%13 = 3 >= 3.
  -- k=2: 6%13 = 6 >= 3.
  -- k=3: 9%13 = 9 >= 3.
  -- k=4: 12%13 = 12 >= 3.
  -- suffices h_ge : 5 ≤ k := by
    -- -- If k ≥ 5, then m = 1342 * k ≥ 1342 * 5 = 6710 = n_min.
    -- have h_final : n_min ≤ m := by
      -- rw [h_m_form]
      -- -- n_min = 1342 * 5
      -- rw [show n_min = 1342 * 5 by rfl]
      -- -- We need 1342 * 5 ≤ 1342 * k
      -- exact Nat.mul_le_mul_left 1342 h_ge

    -- exact h_final

  -- Prove k ≥ 5
  -- By contradiction or case analysis.
  -- Assume k < 5. Since k ≥ 1, k ∈ {1, 2, 3, 4}.
  -- apply lt_irrefl (k:ℕ) -- Wait, standard approach is to show ¬(k < 5)
  -- intro h_k_lt_5
  -- k can be 1, 2, 3, or 4.
  -- have h_check₁ : k = 1 → False := by
    -- intro hk
    -- subst hk
    -- -- Check (3*1)%13 < 3 => 3 < 3 False
    -- have h_bad : ¬((3 * 1) % 13 < 3) := by norm_num
    -- exact h_bad h_k_cond

  -- have h_check₂ : k = 2 → False := by
    -- intro hk
    -- subst hk
    -- -- Check (3*2)%13 < 3 => 6 < 3 False
    -- have h_bad : ¬((3 * 2) % 13 < 3) := by norm_num
    -- exact h_bad h_k_cond

  -- have h_check₃ : k = 3 → False := by
    -- intro hk
    -- subst hk
    -- -- Check (3*3)%13 < 3 => 9 < 3 False
    -- have h_bad : ¬((3 * 3) % 13 < 3) := by norm_num
    -- exact h_bad h_k_cond

  -- have h_check₄ : k = 4 → False := by
    -- intro hk
    -- subst hk
    -- -- Check (3*4)%13 < 3 => 12 < 3 False
    -- have h_bad : ¬((3 * 4) % 13 < 3) := by norm_num
    -- exact h_bad h_k_cond

  -- Case analysis on k
  -- have h_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    -- -- k < 5 and k >= 1 implies k is 1, 2, 3, 4
    -- sorry

  -- cases h_cases with
  -- | inl h => exact h_check₁ h
  -- | inr h =>
    -- cases h with
    -- sorry

  classical
  refine' ⟨h_in_set, fun n h_n => _⟩
  aesop
  by_contra h6
  interval_cases n <;> omega
