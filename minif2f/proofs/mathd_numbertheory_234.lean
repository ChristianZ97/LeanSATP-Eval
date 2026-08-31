
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

theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by
  -- Step 1: Establish that the base of the cube must be 97.
  -- We verify that 97^3 equals the target number.
  have h₂ : 97 ^ 3 = 912673 := by
    norm_num

  -- Step 2: Equate the cubes to imply equality of bases.
  -- Since x^3 is injective for non-negative integers, and we are in Nat,
  -- we can deduce the base is unique.
  -- Specifically, we check that no other natural number near 97 satisfies this.
  -- But simply, since h1 holds and h2 holds, (10*a+b)^3 = 97^3.
  -- Let's explicitly show that 10*a+b must be 97.
  -- We know 90^3 = 729000 and 100^3 = 1000000.
  -- The value 912673 is strictly between these bounds, so the root is between 90 and 100.
  have h₃ : 90 ^ 3 < 912673 := by norm_num
  have h₄ : 912673 < 100 ^ 3 := by norm_num
  -- From h1, h3, h4, we can infer 90 < 10*a+b < 100.
  have h₅ : 90 < 10 * a + b := by
    contrapose! h₃
    norm_num [pow_three] at *
    nlinarith [pow_nonneg (sq_nonneg a) 2, pow_nonneg (sq_nonneg b) 2]

  have h₆ : 10 * a + b < 100 := by
    contrapose! h₄
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 16
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by omega))
      (add safe 0 (by push_neg))
      (add safe 100 (by zify))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [pow_le_pow_left']))
      (add norm 0 (by grind only [bertrand_main_inequality]))
      (add norm 0 (by grind only [one_add_mul_le_pow]))
      (add norm 0 (by grind only [pow_le_pow_left]))
      (add norm 0 (by grind only [sq_le_two_pow_add_one_minus_three]))
      (add norm 0 (by grind only [Finset.sum_condensed_le]))
      (add norm 0 (by grind only [one_le_two]))
      (add norm 0 (by grind only [geom_le]))
      (add norm 0 (by grind only [Finset.sum_condensed_le']))
      (add norm 0 (by grind only [Real.BohrMollerup.f_add_nat_ge]))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [Nat.choose_middle_le_pow]))
      (add norm 0 (by grind only [ack_succ_right_le_ack_succ_left]))
      (add unsafe 10% (by grind only [primorial_le_4_pow]))
      (add unsafe 10% (by grind only [pow_le_pow_of_le_one]))
      (add unsafe 10% (by grind only [pow_le_pow_right]))
      (add unsafe 10% (by grind only [pow_le_pow_right']))
      (add unsafe 10% (by grind only [Nat.pow_le_pow_of_le_left]))
      (add unsafe 10% (by grind only [Nat.le_self_pow]))
      (add unsafe 10% (by grind only [Nat.pow_le_pow_of_le_right]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.merge_lemma]))
      (add unsafe 10% (by grind only [Pell.xn_ge_a_pow]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₄]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₅]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₂]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₁]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₃]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₁]))
      (add unsafe 10% (by grind only [Nat.le_mul_self]))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [SzemerediRegularity.seven_le_initialBound]))
      (add unsafe 10% (by grind only [Nat.le_step]))

  -- Now we know 90 < 10*a+b < 100.
  -- We also check the last digit logic or just brute force check the only candidate 97.
  -- Since the cube function is monotonic, if 97^3 = 912673, then 10*a+b must be 97.
  have h₇ : 10 * a + b = 97 := by
    apply Eq.symm
    -- We prove that the cube root of 912673 in the range [90, 100) is 97.
    -- Since we established the bounds, and verified 97^3, and the function is injective.
    have h₈ : (10 * a + b) ^ 3 = 97 ^ 3 := by
      rw [h₁]
      rw [h₂]

    -- In Lean, we need to extract the root.
    -- We can use the fact that if n^3 = m^3 then n=m for naturals?
    -- Actually, Nat.pow_right_injective isn't always true, but it is for injective powers if we constrain domain?
    -- Easier: Check all possibilities between 90 and 100? No, just use algebraic manipulation or specific lemma.
    -- Let's just use `have` statements to narrow it down or use `decide` on the specific equality after proving bounds.
    -- Better approach: Show that 10*a+b cannot be anything else.
    -- Alternative: Just compute 10*a+b directly using arithmetic if we knew more, but here we rely on h8.
    -- Since we are in Nat, k -> k^3 is not injective globally (e.g. if we allowed negatives, but we don't).
    -- However, it IS injective for Naturals.
    -- Proof: If x^3 = y^3 with x,y >= 0, then x=y.
    -- In Lean Mathlib, this might require some setup.
    -- Let's try to prove x^3 = y^3 -> x = y for Naturals locally or assume it's derivable.
    -- Actually, `Nat.pow_right_injective` requires coprime exponent and modulus usually, or similar conditions.
    -- For prime power p^n | x*y => ...
    -- Simpler: Use the bounds.
    -- We know 90 <= 10*a+b <= 99.
    -- We know (10*a+b)^3 = 97^3.
    -- We can iterate or use logic.
    -- Let's use `interval_cases` on `10*a+b`.
    have h₉ : 10 * a + b ≤ 99 := by
      omega

    have h₁₀ : 10 * a + b ≥ 90 := by
      omega

    interval_cases (10 * a + b) <;> simp_all [pow_three]
    <;> norm_num at *
    <;> try contradiction
    <;> try omega

  -- Step 3: Extract digits a and b from 10*a + b = 97.
  -- Since a and b are digits (b <= 9, a >= 1), the decomposition is unique.
  have h₈ : b = 7 := by
    have h₉ : 10 * a + b = 97 := h₇
    have h₁₀ : b ≤ 9 := h₀.2.2
    have h₁₁ : 1 ≤ a := h₀.1
    -- 10*a = 97 - b
    -- Since b <= 9, 97-b >= 88. So 10*a >= 88 => a >= 9 (since integer).
    -- Since a <= 9, a=9.
    -- If a=9, 10*9+b = 97 => 90+b=97 => b=7.
    have h₁₂ : a ≤ 9 := h₀.2.1
    have h₁₃ : 10 * a ≤ 90 := by
      have h₁₄ : a ≤ 9 := h₁₂
      have h₁₅ : 10 * a ≤ 10 * 9 := by
        exact Nat.mul_le_mul_left 10 h₁₄

      norm_num at h₁₅ ⊢
      exact h₁₅

    have h₁₄ : b = 97 - 10 * a := by
      have h₁₅ : 10 * a + b = 97 := h₇
      have h₁₆ : 10 * a ≤ 97 := by
        -- Since b >= 0 (nat), 10*a <= 10*a+b
        omega

      omega

    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 20
      maxNormIterations := 320
      enableSimp := false
      enableUnfold := false
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
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Nat.sub_add_cancel]))
      (add norm 0 (by grind only [tsub_add_cancel_of_le]))
      (add norm 0 (by grind only [Nat.add_sub_of_le]))
      (add norm 0 (by grind only [add_tsub_cancel_of_le]))
      (add norm 0 (by grind only [tsub_tsub_cancel_of_le]))
      (add norm 0 (by grind only [mul_tsub]))
      (add norm 0 (by grind only [Nat.add_sub_assoc]))
      (add norm 0 (by grind only [tsub_add_eq_add_tsub]))
      (add norm 0 (by grind only [Nat.sub_add_comm]))
      (add norm 0 (by grind only [Nat.add_sub_cancel']))
      (add norm 0 (by grind only [Nat.sub_sub_self]))
      (add norm 0 (by grind only [tsub_tsub]))
      (add norm 0 (by grind only [sub_eq_add]))
      (add norm 0 (by grind only [Nat.psub_eq_sub]))
      (add norm 0 (by grind only [add_tsub_cancel_left]))
      (add norm 0 (by grind only [add_tsub_assoc_of_le]))
      (add norm 0 (by grind only [Nat.sub_eq_zero_of_le]))
      (add norm 0 (by grind only [Nat.even_sub]))
      (add norm 0 (by grind only [eq_tsub_of_add_eq]))
      (add norm 0 (by grind only [eq_tsub_iff_add_eq_of_le]))
      (add norm 0 (by grind only [add_tsub_cancel_right]))
      (add norm 0 (by grind only [SzemerediRegularity.a_add_one_le_four_pow_parts_card]))
      (add norm 0 (by grind only [Nat.sub_le_sub_right]))
      (add norm 0 (by grind only [tsub_tsub_assoc]))
      (add norm 0 (by grind only [tsub_add_tsub_cancel]))
      (add norm 0 (by grind only [le_tsub_of_add_le_right]))
      (add norm 0 (by grind only [tsub_eq_iff_eq_add_of_le]))
      (add norm 0 (by grind only [pow_mul_pow_sub]))
      (add norm 0 (by grind only [Nat.exists_eq_add_of_le]))
      (add unsafe 10% (by grind only [le_tsub_of_add_le_left]))
      (add unsafe 10% (by grind only [Nat.sub_le]))
      (add unsafe 10% (by grind only [Nat.le_sub_one_of_lt]))

  have h₉ : a = 9 := by
    have h₁₀ : 10 * a + b = 97 := h₇
    have h₁₁ : b = 7 := h₈
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
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by zify))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Eq.symm]))
      (add norm 0 (by grind only [Eq.trans]))
      (add norm 0 (by grind only [le_antisymm]))
      (add norm 0 (by grind only [subset_antisymm]))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [Zsqrtd.le_antisymm]))
      (add norm 0 (by grind only [mul_le_mul_of_nonneg_left]))
      (add norm 0 (by grind only [mul_le_mul]))
      (add norm 0 (by grind only [sq_nonneg]))
      (add norm 0 (by grind only [vsub_left_cancel]))
      (add norm 0 (by grind only [one_le_sq_iff]))
      (add norm 0 (by grind only [two_mul_le_add_sq]))
      (add norm 0 (by grind only [mul_le_mul']))
      (add norm 0 (by grind only [eq_of_le_of_not_lt]))
      (add norm 0 (by grind only [sq_le_one_iff]))
      (add norm 0 (by grind only [IsLocalizedModule.finsetIntegerMultiple_image]))
      (add safe 0 (by linarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₁]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 50% (by nlinarith [SzemerediRegularity.seven_le_initialBound]))
      (add unsafe 10% (by grind only [pow_le_pow_right]))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul]))
      (add unsafe 10% (by grind only [Pell.IsFundamental.x_le_x]))
      (add unsafe 50% (by nlinarith [le_mul_of_le_of_one_le]))

  -- Step 4: Calculate sum.
  have h₁₀ : a + b = 16 := by
    have h₁₁ : a = 9 := h₉
    have h₁₂ : b = 7 := h₈
    aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 256
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 0 (by omega))
      (add safe 100 (by zify))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 0 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_le_mul_right']))
      (add norm 0 (by grind only [mul_le_mul_left']))
      (add norm 0 (by grind only [one_le_two]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₁]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.merge_lemma]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₂]))
      (add unsafe 10% (by grind only [le_of_mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₅]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₄]))
      (add unsafe 10% (by grind only [Nat.mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₁]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₃]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.rotateL_lemma₃]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right]))
      (add unsafe 10% (by grind only [le_of_mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [Zsqrtd.sqLe_add_mixed]))
      (add unsafe 50% (by nlinarith [Ordnode.ratio]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₄]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_of_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
      (add unsafe 10% (by grind only [SzemerediRegularity.seven_le_initialBound]))
      (add unsafe 50% (by nlinarith [Ordnode.Valid'.node4L_lemma₂]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))
      (add unsafe 50% (by nlinarith [mul_add_mul_le_mul_add_mul]))
      (add unsafe 50% (by nlinarith [bertrand_main_inequality]))

  exact h₁₀
