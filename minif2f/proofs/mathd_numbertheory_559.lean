
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

theorem mathd_numbertheory_559 :
    IsLeast {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10} 14 := by
  -- Step 1: We want to prove that 14 is the least element of the set.
  -- The set is defined as {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10}
  -- Let's break down the condition for x to be in the set.
  -- Condition 1: 0 < x
  -- Condition 2: x % 3 = 2
  -- Condition 3: ∃ y, y % 5 = 4 ∧ x % 10 = y % 10
  -- From the informal proof, we know that x = 15m + 14 for some integer m >= 0.
  -- This comes from solving the system of congruences:
  -- x ≡ 2 (mod 3)
  -- x ≡ 4 (mod 5)  [since x % 10 = y % 10 and y % 5 = 4 implies x % 5 = 4]
  -- Let's first show that 14 satisfies the conditions.
  have h1 : 0 < (14 : ℕ) := by
    clear * -
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by field_simp [*] at *))
      (add norm 100 (by rfl))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Ordinal.mul_lt_mul_iff_left]))
      (add norm 0 (by grind only [Ordinal.one_lt_omega]))
      (add norm 0 (by grind only [Ordinal.omega_pos]))
      (add norm 0 (by grind only [Ordinal.nat_lt_omega]))
      (add norm 0 (by grind only [Ordinal.opow_pos]))
      (add norm 0 (by grind only [ONote.NFBelow.repr_lt]))
      (add norm 0 (by rw [ONote.repr]))
      (add norm 0 (by grind only [ONote.repr_opow_aux₂]))
      (add norm 0 (by grind only [Ordinal.natCast_lt]))
      (add norm 0 (by grind only [Ordinal.mul_succ]))
      (add norm 0 (by grind only [Ordinal.omega]))
      (add norm 0 (by grind only [Ordinal.opow_succ]))
      (add norm 0 (by grind only [Ordinal.div_lt]))
      (add norm 0 (by grind only [Ordinal.opow_add]))
      (add norm 0 (by grind only [Ordinal.add_absorp]))
      (add norm 0 (by grind only [Ordinal.le_add_right]))
      (add norm 0 (by grind only [Ordinal.le_add_left]))
      (add norm 0 (by grind only [Ordinal.natCast_pos]))
      (add norm 0 (by grind only [ONote.repr_opow_aux₁]))
      (add norm 0 (by rw [Nat.succPNat_coe]))
      (add norm 0 (by grind only [Ordinal.lt_sub]))
      (add norm 0 (by rw [NONote.repr]))
      (add norm 0 (by grind only [Ordinal.opow_mul]))
      (add norm 0 (by rw [Ordinal.opow_one]))
      (add norm 0 (by grind only [Ordinal.lt_omega]))
      (add norm 0 (by grind only [Ordinal.succ_zero]))
      (add norm 0 (by grind only [Ordinal.add_omega_opow]))
      (add norm 0 (by grind only [Ordinal.mul_lt_omega_opow]))
      (add norm 0 (by grind only [Ordinal.opow_lt_opow_iff_right]))
      (add norm 0 (by grind only [Ordinal.omega_ne_zero]))
      (add norm 0 (by rw [Ordinal.natCast_succ]))
      (add norm 0 (by rw [ONote.repr_add]))

  have h2 : (14 : ℕ) % 3 = 2 := by
    clear * -
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 16
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 1 (by ring_nf at *))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by positivity))
      (add unsafe 10% (by grind only [Nat.mul_mod]))
      (add unsafe 10% (by grind only [Nat.mod_two_ne_zero]))
      (add unsafe 10% (by grind only [Nat.mul_mod_left]))
      (add unsafe 10% (by grind only [Nat.mod_two_add_succ_mod_two]))
      (add unsafe 10% (by grind only [Nat.odd_iff]))
      (add unsafe 10% (by grind only [Nat.mod_two_ne_one]))
      (add unsafe 10% (by grind only [Nat.mod_mod]))
      (add unsafe 10% (by grind only [Nat.even_iff]))
      (add unsafe 10% (by grind only [Nat.mod_mod_of_dvd]))
      (add unsafe 10% (by grind only [Nat.mod_mul_left_mod]))
      (add unsafe 10% (by grind only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
      (add unsafe 10% (by grind only [neg_one_pow_eq_pow_mod_two]))
      (add unsafe 10% (by grind only [Nat.mul_mod_mod]))
      (add unsafe 10% (by grind only [Int.emod_two_ne_one]))
      (add unsafe 10% (by grind only [Nat.pow_mod]))
      (add unsafe 10% (by grind only [Nat.mul_mod_right]))
      (add unsafe 10% (by grind only [Nat.mul_mod_mul_left]))
      (add unsafe 10% (by grind only [Int.emod_two_eq_zero_or_one]))
      (add unsafe 10% (by grind only [Nat.mod_two_of_bodd]))
      (add unsafe 10% (by grind only [ZMod.χ₈_nat_eq_if_mod_eight]))
      (add unsafe 10% (by grind only [Int.mul_emod]))
      (add unsafe 10% (by grind only [Nat.gcd.induction]))
      (add unsafe 10% (by grind only [Int.emod_two_ne_zero]))
      (add unsafe 10% (by grind only [Int.odd_iff]))
      (add unsafe 10% (by grind only [Nat.not_even_iff]))
      (add unsafe 10% (by grind only [coprime_sq_sub_sq_sum_of_odd_odd]))
      (add unsafe 10% (by grind only [Nat.mod_mul_mod]))
      (add unsafe 10% (by grind only [Int.ofNat_emod]))
      (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_one_mod_four]))
      (add unsafe 10% (by grind only [Num.dvd_iff_mod_eq_zero]))
      (add unsafe 10% (by grind only [Int.sq_ne_two_mod_four]))
      (add unsafe 10% (by grind only [Int.emod_emod]))

  -- For the third condition, we need to find y such that y % 5 = 4 and 14 % 10 = y % 10.
  -- 14 % 10 = 4. So we need y % 5 = 4 and y % 10 = 4.
  -- Let y = 4. Then 4 % 5 = 4 and 4 % 10 = 4. So this works.
  have h3 : ∃ y : ℕ, y % 5 = 4 ∧ (14 : ℕ) % 10 = y % 10 := by
    let y : ℕ := 4
    have h4 : y % 5 = 4 := by
      clear * -
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 20
        maxNormIterations := 320
        maxGoals := 16
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by omega))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 0 (by ring_nf))
        (add norm 100 (by exfalso))
        (add norm 0 (by ring_nf at *))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by interval_cases))
        (add safe 0 (by ext))
        (add safe 0 (by split))
        (add safe 100 (by simp))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 90% (by positivity))
        (add norm 0 (by grind only [Nat.add_mod]))
        (add norm 0 (by grind only [Nat.add_mod_left]))
        (add norm 0 (by grind only [Nat.mod_add_div]))
        (add norm 0 (by grind only [Nat.mod_two_add_succ_mod_two]))
        (add norm 0 (by grind only [Nat.mul_add_mod]))
        (add unsafe 10% (by grind only [Nat.mod_mod]))
        (add unsafe 10% (by grind only [Nat.mul_mod]))
        (add unsafe 10% (by grind only [Nat.mod_mod_of_dvd]))
        (add unsafe 10% (by grind only [Nat.mod_eq_zero_of_dvd]))
        (add unsafe 10% (by grind only [neg_one_pow_eq_pow_mod_two]))
        (add unsafe 10% (by grind only [Nat.pow_mod]))
        (add unsafe 50% (by nlinarith [Nat.mod_mul_left_mod]))
        (add unsafe 50% (by nlinarith [Nat.mul_mod_left]))
        (add unsafe 10% (by grind only [Nat.odd_iff]))
        (add unsafe 10% (by grind only [Nat.dvd_iff_mod_eq_zero]))
        (add unsafe 10% (by grind only [Nat.ModEq]))
        (add unsafe 10% (by grind only [Nat.gcd.induction]))
        (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_one_mod_four]))
        (add unsafe 50% (by nlinarith [Nat.mul_mod_mod]))
        (add unsafe 50% (by nlinarith [Nat.mul_mod_mul_left]))
        (add unsafe 50% (by nlinarith [Nat.one_mod_of_ne_one]))
        (add unsafe 10% (by grind only [Num.dvd_iff_mod_eq_zero]))
        (add unsafe 50% (by nlinarith [jacobiSym.quadratic_reciprocity_one_mod_four']))
        (add unsafe 50% (by nlinarith [Nat.mul_mod_right]))
        (add unsafe 50% (by nlinarith [Nat.mod_mul_mod]))
        (add unsafe 50% (by nlinarith [Nat.even_iff]))
        (add unsafe 50% (by nlinarith [Nat.mod_two_ne_zero]))
        (add unsafe 10% (by grind only [Num.mod_to_nat]))
        (add unsafe 50% (by nlinarith [Nat.mod_two_of_bodd]))
        (add unsafe 10% (by grind only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
        (add unsafe 10% (by grind only [PNat.mod_coe]))
        (add unsafe 50% (by nlinarith [Nat.mod_two_ne_one]))

    have h5 : (14 : ℕ) % 10 = y % 10 := by
      clear * - h4
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
        (add norm 0 (by ring_nf))
        (add norm 0 (by ring_nf at *))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by push_neg))
        (add safe 100 (by interval_cases))
        (add safe 0 (by ext))
        (add safe 100 (by simp))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 90% (by positivity))
        (add norm 0 (by grind only [Nat.add_mod]))
        (add norm 0 (by grind only [Nat.add_mod_left]))
        (add unsafe 10% (by grind only [Nat.mod_mod]))
        (add unsafe 10% (by grind only [Nat.mod_mod_of_dvd]))
        (add unsafe 10% (by grind only [Nat.mul_mod]))
        (add unsafe 10% (by grind only [Nat.mod_eq_zero_of_dvd]))
        (add unsafe 10% (by grind only [Nat.dvd_iff_mod_eq_zero]))
        (add unsafe 10% (by grind only [Nat.mod_mul_left_mod]))
        (add unsafe 10% (by grind only [Nat.pow_mod]))
        (add unsafe 10% (by grind only [Nat.one_mod_of_ne_one]))
        (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_one_mod_four]))
        (add unsafe 10% (by grind only [neg_one_pow_eq_pow_mod_two]))
        (add unsafe 10% (by grind only [Nat.odd_iff]))
        (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_one_mod_four']))
        (add unsafe 10% (by grind only [Num.dvd_iff_mod_eq_zero]))
        (add unsafe 10% (by grind only [Nat.mod_mul_mod]))
        (add unsafe 10% (by grind only [Nat.ModEq]))
        (add unsafe 10% (by grind only [Num.mod_to_nat]))
        (add unsafe 10% (by grind only [Nat.mul_mod_mod]))
        (add unsafe 10% (by grind only [Nat.mul_mod_left]))
        (add unsafe 10% (by grind only [Nat.mod_lt]))
        (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_if]))
        (add unsafe 10% (by grind only [Nat.mod_two_ne_zero]))
        (add unsafe 10% (by grind only [PNat.mod_coe]))
        (add unsafe 10% (by grind only [Nat.gcd.induction]))
        (add unsafe 10% (by grind only [jacobiSym.even_odd]))
        (add unsafe 10% (by grind only [Nat.even_iff]))
        (add unsafe 50% (by nlinarith [Nat.mul_mod_mul_left]))
        (add unsafe 10% (by grind only [Nat.zero_mod]))
        (add unsafe 10% (by grind only [Nat.mod_two_ne_one]))
        (add unsafe 50% (by nlinarith [Nat.mul_mod_right]))
        (add unsafe 10% (by grind only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))

    clear * - h4 h5
    repeat'
    first
    | constructor
    | assumption

  -- Now we have shown that 14 is in the set.
  have h6 : (14 : ℕ) ∈ {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10} := by
    clear * - h1 h2 h3
    exact ⟨h1, h2, 4, by trivial⟩

  -- Now we need to show that 14 is the least element.
  -- That is, for any x in the set, x >= 14.
  -- From the informal proof, we derived that x = 15m + 14 for m >= 0.
  -- The smallest value is when m = 0, giving x = 14.
  -- Let's formalize the relationship between the conditions and the form x = 15m + 14.
  -- First, let's understand what the condition ∃ y, y % 5 = 4 ∧ x % 10 = y % 10 means.
  -- If y % 5 = 4, then y can be written as 5k + 4 for some integer k.
  -- Also, x % 10 = y % 10.
  -- Since y = 5k + 4, y % 10 depends on k mod 2.
  -- If k is even, say k = 2j, then y = 10j + 4, so y % 10 = 4.
  -- If k is odd, say k = 2j + 1, then y = 10j + 9, so y % 10 = 9.
  -- So x % 10 must be either 4 or 9.
  -- But also, from x ≡ 2 (mod 3), we have x % 3 = 2.
  -- Let's check which values of x satisfy both x % 3 = 2 and x % 10 ∈ {4, 9}.
  -- Actually, from the informal proof, it seems they assumed x % 5 = 4 directly.
  -- Let's verify: if x % 10 = y % 10 and y % 5 = 4, does this imply x % 5 = 4?
  -- Yes, because x % 10 = y % 10 implies x ≡ y (mod 10), which implies x ≡ y (mod 5).
  -- Since y % 5 = 4, we have x % 5 = 4.
  have h7 : ∀ x : ℕ, x ∈ {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10} →
    x % 5 = 4 := by
    intro x hx
    cases' hx with h_pos h_and
    cases' h_and with h_mod3 h_exists
    cases' h_exists with y h_y_conditions
    cases' h_y_conditions with h_y_mod5 h_x_eq_y_mod10
    -- We have y % 5 = 4 and x % 10 = y % 10.
    -- We want to show x % 5 = 4.
    have h8 : x % 5 = 4 := by
      clear * - h_y_mod5 h_x_eq_y_mod10
      aesop (config := {
        maxRuleApplications := 40
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        })
        (add norm 100 (by field_simp))
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
        (add safe 100 (by norm_num))
        (add safe 0 (by gcongr))
        (add safe 100 (by interval_cases))
        (add safe 0 (by ext))
        (add safe 0 (by split))
        (add safe 100 (by simp))
        (add safe 0 (by norm_num [*] at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add unsafe 90% (by positivity))
        (add safe 0 (by simp_all [Int.natCast_mod]))
        (add unsafe 10% (by grind only [Nat.mod_mod_of_dvd]))
        (add unsafe 10% (by grind only [Nat.mod_mod]))
        (add unsafe 10% (by grind only [Nat.mul_mod]))
        (add unsafe 10% (by grind only [Nat.pow_mod]))
        (add unsafe 10% (by grind only [Nat.mod_mul_left_mod]))
        (add unsafe 10% (by grind only [Nat.mul_mod_mod]))
        (add unsafe 10% (by grind only [Nat.mod_eq_zero_of_dvd]))
        (add unsafe 10% (by grind only [Num.dvd_iff_mod_eq_zero]))
        (add unsafe 10% (by grind only [Nat.dvd_iff_mod_eq_zero]))
        (add unsafe 10% (by grind only [Num.mod_to_nat]))
        (add unsafe 10% (by grind only [Nat.odd_iff]))
        (add unsafe 10% (by grind only [Nat.one_mod_of_ne_one]))
        (add unsafe 10% (by grind only [Nat.mod_mul_mod]))
        (add unsafe 10% (by grind only [Nat.gcd.induction]))
        (add unsafe 10% (by grind only [Nat.ModEq]))
        (add unsafe 50% (by nlinarith [Nat.mul_mod_left]))
        (add unsafe 10% (by grind only [Nat.mod_two_ne_zero]))
        (add unsafe 10% (by grind only [neg_one_pow_eq_pow_mod_two]))
        (add unsafe 10% (by grind only [PNat.mod_coe]))
        (add unsafe 10% (by grind only [Int.emod_emod_of_dvd]))
        (add unsafe 10% (by grind only [GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]))
        (add unsafe 10% (by grind only [Int.ofNat_emod]))
        (add unsafe 10% (by grind only [Int.mul_emod]))
        (add unsafe 10% (by grind only [Int.emod_emod]))
        (add unsafe 10% (by grind only [Nat.even_iff]))
        (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_one_mod_four]))
        (add unsafe 10% (by grind only [Nat.mod_two_ne_one]))
        (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_one_mod_four']))
        (add unsafe 10% (by grind only [Nat.ofDigits_zmod]))
        (add unsafe 50% (by nlinarith [Nat.mul_mod_mul_left]))
        (add unsafe 50% (by nlinarith [Nat.mul_mod_right]))

    exact h8

  -- Now we have x % 3 = 2 and x % 5 = 4.
  -- By Chinese Remainder Theorem, since gcd(3, 5) = 1, there is a unique solution modulo 15.
  -- From the informal proof, we found x ≡ 14 (mod 15).
  have h9 : ∀ x : ℕ, x ∈ {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10} →
    x % 15 = 14 := by
    intro x hx
    cases' hx with h_pos h_and
    cases' h_and with h_mod3 h_exists
    cases' h_exists with y h_y_conditions
    cases' h_y_conditions with h_y_mod5 h_x_eq_y_mod10
    have h10 : x % 3 = 2 := h_mod3
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      useDefaultSimpSet := false
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
      (add safe 0 (by positivity))
      (add safe 100 (by push_neg))
      (add safe 0 (by gcongr))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.mod_add_div]))
      (add norm 0 (by grind only [Nat.div_add_mod]))
      (add norm 0 (by grind only [Nat.add_mod]))
      (add unsafe 10% (by grind only [Nat.mod_lt]))
      (add unsafe 10% (by grind only [Nat.mod_le]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem2]))
      (add unsafe 10% (by grind only [Num.mod_to_nat]))
      (add unsafe 10% (by grind only [Nat.ModEq]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem3]))
      (add unsafe 10% (by grind only [Pell.strictMono_x]))
      (add unsafe 10% (by grind only [Nat.mod_mod]))
      (add unsafe 10% (by grind only [PNat.XgcdType.r]))
      (add unsafe 10% (by grind only [Nat.mod_mod_of_dvd]))
      (add unsafe 10% (by grind only [Pell.xn]))
      (add unsafe 10% (by grind only [Nat.mod_injOn_Ico]))
      (add unsafe 10% (by grind only [jacobiSym.mod_left]))
      (add unsafe 10% (by grind only [Nat.mul_mod]))
      (add unsafe 10% (by grind only [Nat.dvd_iff_mod_eq_zero]))
      (add unsafe 10% (by grind only [jacobiSym.even_odd]))
      (add unsafe 10% (by grind only [modEq_mersenne]))
      (add unsafe 10% (by grind only [Int.emod_emod_of_dvd]))
      (add unsafe 10% (by grind only [Nat.mod_modEq]))
      (add unsafe 10% (by grind only [Pell.strictMono_y]))
      (add unsafe 10% (by grind only [Nat.mod_eq_zero_of_dvd]))
      (add unsafe 10% (by grind only [ZMod.eisenstein_lemma_aux]))
      (add unsafe 10% (by grind only [Pell.x_pos]))
      (add unsafe 10% (by grind only [Nat.mod_mul_mod]))
      (add unsafe 10% (by grind only [Nat.gcd.induction]))
      (add unsafe 10% (by grind only [Int.emod_eq_of_lt]))
      (add unsafe 50% (by nlinarith [Nat.mod_mul_left_mod]))
      (add unsafe 10% (by grind only [Num.dvd_iff_mod_eq_zero]))
      (add unsafe 10% (by grind only [jacobiSym.quadratic_reciprocity_if]))

  -- Now, if x % 15 = 14 and x > 0, then x can be written as 15m + 14 for some m ≥ 0.
  -- The smallest positive value is when m = 0, giving x = 14.
  have h13 : ∀ x : ℕ, x ∈ {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10} →
    x ≥ 14 := by
    intro x hx
    cases' hx with h_pos h_and
    cases' h_and with h_mod3 h_exists
    cases' h_exists with y h_y_conditions
    cases' h_y_conditions with h_y_mod5 h_x_eq_y_mod10
    aesop (config := {
      maxRuleApplications := 100
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
      (add safe 0 (by positivity))
      (add safe 100 (by push_neg))
      (add safe 0 (by split))
      (add safe 100 (by simp))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by grind only [Nat.mod_lt]))
      (add unsafe 10% (by grind only [Pell.strictMono_x]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem3]))
      (add unsafe 10% (by grind only [Pell.x_pos]))
      (add unsafe 10% (by grind only [Nat.mod_le]))
      (add unsafe 10% (by grind only [Nat.succ_le_of_lt]))
      (add unsafe 10% (by grind only [Pell.d_pos]))
      (add unsafe 10% (by grind only [Pell.yn_ge_n]))
      (add unsafe 10% (by grind only [Pell.strictMono_y]))
      (add unsafe 10% (by grind only [Pell.xn]))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
      (add unsafe 10% (by grind only [Pell.eq_of_xn_modEq_lem1]))
      (add unsafe 10% (by grind only [Nat.le_of_lt_succ]))
      (add unsafe 10% (by grind only [Nat.lt_of_succ_le]))
      (add unsafe 10% (by grind only [Ordnode.Sized.pos]))
      (add unsafe 10% (by grind only [lt_of_le_of_ne]))
      (add unsafe 10% (by grind only [Nat.zero_le]))
      (add unsafe 10% (by grind only [Num.cast_lt]))
      (add unsafe 10% (by grind only [Nat.le_of_dvd]))
      (add unsafe 10% (by grind only [Nat.succ_le_iff]))
      (add unsafe 10% (by grind only [Nat.lt_succ_of_le]))
      (add unsafe 10% (by grind only [Nat.le_of_mod_lt]))
      (add unsafe 10% (by grind only [Pell.n_lt_xn]))
      (add unsafe 10% (by grind only [Nat.mul_div_lt_iff_not_dvd]))
      (add unsafe 10% (by grind only [Nat.le_succ_of_le]))
      (add unsafe 10% (by grind only [Num.cast_le]))
      (add unsafe 10% (by grind only [Nat.succ_le]))
      (add unsafe 10% (by grind only [Nat.div_lt_self]))
      (add unsafe 10% (by grind only [Ordnode.Valid'.rotateL_lemma₂]))
      (add unsafe 10% (by grind only [Num.le_to_nat]))
      (add unsafe 10% (by grind only [not_le_of_lt]))
      (add unsafe 10% (by grind only [MulAction.le_period]))

  -- Finally, we combine these results to show that 14 is the least element.
  simp [IsLeast, lowerBounds, IsMin]
  constructor <;> aesop
