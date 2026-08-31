
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

theorem amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) (h₁ : 4 ≤ p ∧ p ≤ 18)
    (h₂ : 4 ≤ q ∧ q ≤ 18) : ↑p * ↑q - (↑p + ↑q : ℤ) ≠ (194 : ℤ) := by
  -- Step 1 & 2 & 3: Derive (p-1)(q-1) = 195 from pq - (p+q) = 194
  have h_step3_eq : (↑p - 1 : ℤ) * (↑q - 1 : ℤ) = (195 : ℤ) → ↑p * ↑q - (↑p + ↑q : ℤ) = (194 : ℤ) := by
    intro h
    ring_nf at h ⊢
    linarith

  -- Step 8: Factorization of 195
  have h_fact : 195 = 3 * 5 * 13 := by norm_num
  -- Step 4, 6: Bounds on p and q
  have h_p_lower : 4 ≤ p := by
    exact h₁.1

  have h_p_upper : p ≤ 18 := by
    exact h₁.2

  have h_q_lower : 4 ≤ q := by
    exact h₂.1

  have h_q_upper : q ≤ 18 := by
    exact h₂.2

  -- Step 5, 7: Bounds on p-1 and q-1
  have h_pm1_lower : 3 ≤ (↑p - 1 : ℤ) := by
    have hp : (4 : ℤ) ≤ ↑p := by exact_mod_cast h_p_lower
    linarith

  have h_pm1_upper : (↑p - 1 : ℤ) ≤ 17 := by
    have hp : ↑p ≤ (18 : ℤ) := by exact_mod_cast h_p_upper
    linarith

  have h_qm1_lower : 3 ≤ (↑q - 1 : ℤ) := by
    have hq : (4 : ℤ) ≤ ↑q := by exact_mod_cast h_q_lower
    linarith

  have h_qm1_upper : (↑q - 1 : ℤ) ≤ 17 := by
    have hq : ↑q ≤ (18 : ℤ) := by exact_mod_cast h_q_upper
    linarith

  -- Assume for contradiction that pq - (p+q) = 194
  by_contra h_contr
  -- If pq - (p+q) = 194, then (p-1)(q-1) = 195
  have h_prod_195 : (↑p - 1 : ℤ) * (↑q - 1 : ℤ) = (195 : ℤ) := by
    have h_eq : ↑p * ↑q - (↑p + ↑q : ℤ) = (194 : ℤ) := by
      simpa using h_contr

    have h_rearrange : (↑p - 1 : ℤ) * (↑q - 1 : ℤ) = ↑p * ↑q - (↑p + ↑q : ℤ) + 1 := by
      ring

    rw [h_rearrange]
    rw [h_eq]
    norm_num

  -- From factors of 195 and bounds, determine possible values for p-1
  -- Divisors of 195 are 1, 3, 5, 13, 15, 39, 65, 195
  -- Given 3 <= p-1 <= 17, possible p-1 are 3, 5, 13, 15
  -- Case analysis on p-1
  have h_pm1_cases : (↑p - 1 : ℤ) = 3 ∨ (↑p - 1 : ℤ) = 5 ∨ (↑p - 1 : ℤ) = 13 ∨ (↑p - 1 : ℤ) = 15 := by
    have h1 : (↑p - 1 : ℤ) ∣ 195 := by
      use ↑q - 1 <;> nlinarith

    have h2 : 3 ≤ (↑p - 1 : ℤ) := h_pm1_lower
    have h3 : (↑p - 1 : ℤ) ≤ 17 := h_pm1_upper
    interval_cases hpf : (p : ℤ) - 1 <;> simp_all (config := { decide := true })

  -- Instead of generic divisors, let's use the explicit steps from informal proof
  -- Informal step 9 says: p-1 = 13 or p-1 = 15
  -- Why? Because q-1 must also be in [3, 17].
  -- If p-1 = 3, q-1 = 65 (not in [3,17])
  -- If p-1 = 5, q-1 = 39 (not in [3,17])
  -- If p-1 = 13, q-1 = 15 (in [3,17]) -> Valid pair
  -- If p-1 = 15, q-1 = 13 (in [3,17]) -> Valid pair
  have h_p_val_cases : p = 14 ∨ p = 16 := by
    have h_divs : ((↑p - 1 : ℤ) = 13 ∨ (↑p - 1 : ℤ) = 15) := by
      -- Proof that only 13 and 15 work given q-1 constraints
      have h_pair : (↑q - 1 : ℤ) = 195 / (↑p - 1 : ℤ) := by
        apply Eq.symm
        aesop (config := {
          maxRuleApplications := 100
          maxRuleApplicationDepth := 20
          maxNormIterations := 320
          maxGoals := 512
          useDefaultSimpSet := false
          })
          (add norm 100 (by norm_cast))
          (add norm 0 (by linarith))
          (add norm 0 (by nlinarith))
          (add norm 0 (by omega))
          (add norm 1 (by push_neg))
          (add norm 0 (by bound))
          (add norm 1 (by ext))
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
          (add norm 0 (by grind only [Nat.mul_div_cancel']))
          (add norm 0 (by grind only [Nat.mul_div_cancel_left]))
          (add norm 0 (by grind only [Int.mul_ediv_cancel']))
          (add norm 0 (by grind only [div_mul_div_cancel]))
          (add norm 0 (by grind only [div_left_inj']))
          (add norm 0 (by grind only [Nat.mul_div_cancel]))
          (add norm 0 (by grind only [Nat.div_mul_cancel]))
          (add norm 0 (by grind only [mul_div_assoc']))
          (add norm 0 (by grind only [Nat.mul_div_left]))
          (add norm 0 (by grind only [EuclideanDomain.eq_div_of_mul_eq_left]))
          (add norm 0 (by grind only [div_eq_div_iff]))
          (add norm 0 (by grind only [Nat.mul_div_cancel_left']))
          (add norm 0 (by grind only [Nat.cast_div]))
          (add norm 0 (by grind only [mul_div_right_comm]))
          (add norm 0 (by grind only [mul_div_left_comm]))
          (add norm 0 (by grind only [Nat.div_div_self]))
          (add safe 0 (by simp only [eq_div_iff] at *))
          (add safe 0 (by simp only [div_mul_cancel₀] at *))
          (add safe 0 (by simp only [mul_div_cancel₀] at *))
          (add safe 0 (by simp only [div_eq_iff] at *))
          (add safe 0 (by simp only [mul_div_cancel_right₀] at *))
          (add safe 0 (by simp only [eq_div_iff_mul_eq] at *))
          (add safe 0 (by simp only [mul_div] at *))
          (add safe 0 (by simp only [mul_div_assoc] at *))
          (add safe 0 (by simp only [mul_div_cancel_left₀] at *))
          (add safe 0 (by simp only [div_eq_one_iff_eq] at *))
          (add safe 0 (by simp only [div_self] at *))
          (add safe 0 (by simp only [mul_div_mul_left] at *))
          (add safe 0 (by simp only [div_eq_iff_mul_eq] at *))
          (add safe 0 (by simp only [div_div] at *))
          (add safe 0 (by simp only [add_div] at *))
          (add safe 0 (by simp only [mul_div_mul_right] at *))

      by_cases h13 : (↑p - 1 : ℤ) = 13
      · left; exact h13
      · by_cases h15 : (↑p - 1 : ℤ) = 15
        · right; exact h15
        · -- Check other divisors 3, 5
          by_cases h3 : (↑p - 1 : ℤ) = 3
          · exfalso
            have hq_val : (↑q - 1 : ℤ) = 65 := by
              rw [h_pair]; norm_num [h3]

            have hq_bound : (↑q - 1 : ℤ) ≤ 17 := h_qm1_upper
            linarith

          · by_cases h5 : (↑p - 1 : ℤ) = 5
            · exfalso
              have hq_val : (↑q - 1 : ℤ) = 39 := by
                rw [h_pair]; norm_num [h5]

              have hq_bound : (↑q - 1 : ℤ) ≤ 17 := h_qm1_upper
              linarith

            · -- Must be 13 or 15 because others don't divide 195 within range or result in out-of-range q-1
              -- We already ruled out 3, 5. What about others?
              -- The divisors in [3, 17] are 3, 5, 13, 15.
              -- So it must be one of these.
              have h_in_range : (↑p - 1 : ℤ) ∈ ({3, 5, 13, 15} : Set ℤ) := by
                aesop (config := {
                  maxRuleApplications := 1600
                  maxRuleApplicationDepth := 20
                  maxNormIterations := 320
                  })
                  (add norm 100 (by norm_cast))
                  (add norm 0 (by linarith))
                  (add norm 0 (by nlinarith))
                  (add norm 0 (by omega))
                  (add norm 0 (by bound))
                  (add norm 1 (by ext))
                  (add norm 100 (by ring_nf at *))
                  (add norm 1 (by field_simp [*] at *))
                  (add safe 100 (by ring))
                  (add safe 100 (by field_simp))
                  (add safe 100 (by norm_num))
                  (add safe 100 (by positivity))
                  (add safe 100 (by push_neg))
                  (add safe 100 (by interval_cases))
                  (add safe 0 (by split))
                  (add safe 0 (by exfalso))
                  (add safe 100 (by rfl))
                  (add safe 100 (by decide))
                  (add safe 0 (by push_cast))
                  (add safe 100 (by assumption_mod_cast))
                  (add norm 0 (by grind only [Finset.mem_singleton]))
                  (add norm 0 (by grind only [Set.mem_singleton_iff]))
                  (add norm 0 (by grind only [Set.mem_insert_iff]))
                  (add norm 0 (by grind only [Finset.mem_insert]))
                  (add norm 0 (by grind only [Finset.mem_singleton_self]))
                  (add norm 0 (by grind only [SimpleGraph.is3Clique_triple_iff]))
                  (add norm 0 (by grind only [ZFSet.mem_insert_iff]))
                  (add norm 0 (by grind only [SimpleGraph.mk'_mem_incidenceSet_iff]))
                  (add norm 0 (by grind only [Finmap.mem_insert]))
                  (add norm 0 (by grind only [mul_not_mem_of_exponent_two]))
                  (add norm 0 (by grind only [Set.mem_singleton]))
                  (add norm 0 (by grind only [forall_eq]))
                  (add norm 0 (by grind only [AList.mem_insert]))
                  (add norm 0 (by grind only [Set.eq_of_mem_singleton]))
                  (add norm 0 (by grind only [Finset.mem_union]))
                  (add norm 0 (by grind only [Turing.TM2.stmts₁_self]))
                  (add norm 0 (by grind only [FirstOrder.Language.Theory.model_iff]))
                  (add norm 0 (by grind only [Turing.TM1.stmts₁_self]))
                  (add norm 0 (by grind only [Set.equitableOn_singleton]))
                  (add norm 0 (by grind only [Turing.PartrecToTM2.trStmts₁_self]))
                  (add norm 0 (by grind only [Turing.TM1.stmts₁]))
                  (add norm 0 (by grind only [true_or]))
                  (add norm 0 (by grind only [ZFSet.mem_pair]))
                  (add norm 0 (by grind only [SimpleGraph.mem_edgeSet]))
                  (add norm 0 (by grind only [ZFSet.mem_singleton]))
                  (add norm 0 (by grind only [Set.union_singleton]))
                  (add norm 0 (by grind only [Finset.mem_insert_self]))
                  (add norm 0 (by grind only [mul_not_mem_of_orderOf_eq_two]))
                  (add norm 0 (by grind only [Multiset.mem_singleton]))
                  (add norm 0 (by grind only [SimpleGraph.mem_incidenceSet]))
                  (add norm 0 (by grind only [FirstOrder.Language.Theory.model_singleton_iff]))
                  (add norm 0 (by grind only [Turing.TM2.stmts₁]))

              aesop (config := {
                maxRuleApplications := 1600
                maxRuleApplicationDepth := 20
                maxNormIterations := 320
                useDefaultSimpSet := false
                })
                (add norm 100 (by norm_cast))
                (add norm 0 (by linarith))
                (add norm 0 (by nlinarith))
                (add norm 0 (by omega))
                (add norm 0 (by bound))
                (add norm 1 (by ext))
                (add norm 1 (by field_simp [*] at *))
                (add safe 100 (by ring))
                (add safe 100 (by field_simp))
                (add safe 100 (by norm_num))
                (add safe 100 (by positivity))
                (add safe 0 (by push_neg))
                (add safe 100 (by interval_cases))
                (add safe 0 (by split))
                (add safe 0 (by exfalso))
                (add safe 1 (by ring_nf at *))
                (add safe 100 (by norm_cast at *))
                (add safe 100 (by rfl))
                (add safe 100 (by decide))
                (add safe 0 (by push_cast))
                (add safe 100 (by assumption_mod_cast))
                (add norm 0 (by grind only [Set.mem_insert_iff]))
                (add norm 0 (by grind only [true_or]))
                (add norm 0 (by grind only [or_not]))
                (add norm 0 (by grind only [or_true]))
                (add norm 0 (by grind only [ZFSet.mem_insert_iff]))
                (add norm 0 (by grind only [Set.mem_singleton_iff]))
                (add norm 0 (by grind only [Finset.mem_singleton]))
                (add norm 0 (by grind only [Finset.mem_insert]))
                (add norm 0 (by grind only [AList.mem_insert]))
                (add norm 0 (by grind only [Finmap.mem_insert]))
                (add norm 0 (by grind only [ZFSet.mem_pair]))
                (add norm 0 (by grind only [Finset.mem_union]))
                (add norm 0 (by grind only [SimpleGraph.mk'_mem_incidenceSet_iff]))
                (add norm 0 (by grind only [true_or_iff]))
                (add norm 0 (by grind only [or_true_iff]))
                (add norm 0 (by grind only [Finset.mem_singleton_self]))
                (add norm 0 (by rw [Ordnode.size_balanceR]))
                (add unsafe 10% (by grind only [Or]))
                (add unsafe 10% (by grind only [Or.elim]))
                (add unsafe 10% (by grind only [FiniteInter.finiteInterClosure_insert]))
                (add unsafe 10% (by grind only [Beatty.hit_or_miss']))
                (add unsafe 10% (by grind only [And]))
                (add unsafe 10% (by grind only [Or.imp]))
                (add unsafe 10% (by grind only [Beatty.hit_or_miss]))
                (add unsafe 10% (by grind only [SzemerediRegularity.card_eq_of_mem_parts_chunk]))
                (add unsafe 10% (by grind only [SimpleGraph.Walk.IsEulerian.card_filter_odd_degree]))
                (add unsafe 10% (by grind only [Or.intro_right]))
                (add unsafe 10% (by grind only [Or.symm]))
                (add unsafe 10% (by grind only [Or.intro_left]))
                (add unsafe 10% (by grind only [DirichletCharacter.even_or_odd]))
                (add unsafe 10% (by grind only [Or.imp_right]))
                (add unsafe 10% (by grind only [Or.imp_left]))

      -- If p-1=13, q-1=15. Both in range.
      -- If p-1=15, q-1=13. Both in range.

    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 600
      maxNormIterations := 320
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 0 (by push_neg))
      (add safe 0 (by gcongr))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by exfalso))
      (add safe 1 (by ring_nf at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by grind only [Or]))
      (add unsafe 10% (by grind only [Or.elim]))
      (add unsafe 10% (by grind only [FiniteInter.finiteInterClosure_insert]))
      (add unsafe 10% (by grind only [Or.imp]))
      (add unsafe 10% (by grind only [Beatty.hit_or_miss']))
      (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_lt]))
      (add unsafe 10% (by grind only [SimpleGraph.Walk.IsEulerian.card_filter_odd_degree]))
      (add unsafe 10% (by grind only [Nat.eq_zero_or_pos]))
      (add unsafe 10% (by grind only [Or.intro_right]))
      (add unsafe 10% (by grind only [Or.symm]))
      (add unsafe 10% (by grind only [And]))
      (add unsafe 10% (by grind only [Or.imp_right]))
      (add unsafe 10% (by grind only [Or.intro_left]))
      (add unsafe 10% (by grind only [Beatty.hit_or_miss]))
      (add unsafe 10% (by grind only [DirichletCharacter.even_or_odd]))
      (add unsafe 10% (by grind only [Or.imp_left]))
      (add unsafe 10% (by grind only [Ordnode.Raised]))
      (add unsafe 10% (by grind only [EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two]))
      (add unsafe 10% (by grind only [EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two]))
      (add unsafe 10% (by grind only [IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd]))
      (add unsafe 10% (by grind only [Set.not_mem_uIcc_of_gt]))
      (add unsafe 10% (by grind only [SzemerediRegularity.card_eq_of_mem_parts_chunk]))
      (add unsafe 10% (by grind only [Ordnode.size_balanceR]))
      (add unsafe 10% (by grind only [Ordnode.pos_size_of_mem]))
      (add unsafe 10% (by grind only [Ordnode.size_balanceL]))
      (add unsafe 10% (by grind only [Compactum.join_distrib]))
      (add unsafe 10% (by grind only [Ordnode.Raised.add_left]))
      (add unsafe 10% (by grind only [Ideal.IsPrime.mem_or_mem]))
      (add unsafe 10% (by grind only [EuclideanGeometry.dist_div_sin_oangle_left_of_oangle_eq_pi_div_two]))
      (add unsafe 10% (by grind only [or_not]))
      (add unsafe 10% (by grind only [And.imp_right]))
      (add unsafe 10% (by grind only [EuclideanGeometry.dist_div_sin_oangle_right_of_oangle_eq_pi_div_two]))

  -- Step 11, 12: Check primality
  have h_not_prime_14 : ¬Nat.Prime 14 := by norm_num
  have h_not_prime_16 : ¬Nat.Prime 16 := by norm_num
  -- Step 13: p is not prime
  have h_p_not_prime : ¬Nat.Prime p := by
    cases h_p_val_cases with
    | inl h14 =>
      have hp : p = 14 := by simpa using h14
      rw [hp]
      exact h_not_prime_14

    | inr h16 =>
      have hp : p = 16 := by simpa using h16
      rw [hp]
      exact h_not_prime_16

  -- Contradiction with h₀
  have h_p_is_prime : Nat.Prime p := h₀.1
  exact h_p_not_prime h_p_is_prime
