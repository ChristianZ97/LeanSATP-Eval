
import Mathlib

set_option maxHeartbeats 0

abbrev putnam_1986_a2_solution : ℕ := 3
theorem putnam_1986_a2
: (Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10 = putnam_1986_a2_solution) := by
  have h_main : Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10 = 3 := by
    -- Let y = 10^100. We are analyzing floor(y^200 / (y+3)) mod 10.
    -- Note that 10^20000 = (10^100)^200.
    let y : ℝ := 10 ^ 100
    have h_y_pow : y ^ 200 = (10 ^ 20000 : ℝ) := by
      norm_num [pow_mul]
      <;> ring_nf
      aesop (config := {
        maxRuleApplications := 100
        maxRuleApplicationDepth := 10
        maxNormIterations := 320
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 1 (by push_neg))
        (add norm 0 (by bound))
        (add norm 1 (by ring_nf))
        (add norm 1 (by simp))
        (add norm 100 (by simp_all))
        (add norm 1 (by field_simp [*] at *))
        (add norm 1 (by norm_num [*] at *))
        (add safe 100 (by ring))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 100 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 0 (by split))
        (add safe 0 (by exfalso))
        (add safe 100 (by norm_cast at *))
        (add safe 100 (by decide))
        (add safe 0 (by push_cast))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [MulZeroClass]))
        (add norm 0 (by grind only [SzemerediRegularity.eps_pow_five_pos]))
        (add norm 0 (by grind only [Nat.cast_zero]))
        (add norm 0 (by grind only [FractionalIdeal.div_zero]))
        (add norm 0 (by grind only [EuclideanDomain.zero_div]))
        (add norm 0 (by grind only [Zsqrtd.zero_re]))
        (add norm 0 (by grind only [div_zero]))
        (add norm 0 (by grind only [Zsqrtd.zero_im]))
        (add norm 0 (by grind only [Rat.zero_divInt]))
        (add norm 0 (by grind only [quadraticChar_zero]))
        (add norm 0 (by grind only [jacobiSym.zero_left]))
        (add norm 0 (by grind only [zero_pow]))
        (add norm 0 (by grind only [Ordinal.zero_opow]))
        (add norm 0 (by grind only [Real.sqrt_pos]))
        (add norm 0 (by grind only [HasDerivWithinAt.deriv_eq_zero]))
        (add norm 0 (by grind only [HurwitzZeta.evenKernel_undef]))
        (add norm 0 (by grind only [Int.zero_mul]))
        (add norm 0 (by grind only [Real.sqrt_zero]))
        (add norm 0 (by grind only [Ordinal.div_zero]))
        (add norm 0 (by grind only [ZNum.div_zero]))
        (add norm 0 (by grind only [MulChar.map_zero]))
        (add norm 0 (by grind only [EReal.zero_div]))
        (add norm 0 (by grind only [zero_tsub]))
        (add norm 0 (by grind only [Int.zero_ediv]))
        (add unsafe 10% (by grind only [LucasLehmer.mersenne_int_pos]))
        (add unsafe 10% (by grind only [Nat.cast_pos]))
        (add unsafe 50% (by nlinarith [Int.ediv_zero]))
        (add unsafe 50% (by nlinarith [mul_self_pos]))
        (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_right]))
        (add unsafe 10% (by grind only [Int.natCast_pos]))
        (add unsafe 50% (by nlinarith [mul_pos_iff_of_pos_left]))
        (add unsafe 10% (by grind only [Int.natCast_nonpos_iff]))

    have h_divisor : (10 ^ 100 + 3 : ℝ) = y + 3 := by
      rfl

    have h_expr : (10 ^ 20000 : ℝ) / (10 ^ 100 + 3) = y ^ 200 / (y + 3) := by
      rw [h_y_pow, h_divisor]

    -- We use the algebraic identity: x^n - a^n = (x-a)(x^(n-1) + x^(n-2)a + ... + a^(n-1))
    -- Here we want to divide y^200 by y+3.
    -- Consider P(y) such that y^200 = (y+3)P(y) + R.
    -- By polynomial division, R = (-3)^200 = 3^200.
    -- So y^200 = (y+3)Q(y) + 3^200, where Q(y) = sum_{k=0}^{199} y^(199-k)*(-3)^k.
    -- Thus y^200 / (y+3) = Q(y) + 3^200 / (y+3).
    -- Since y = 10^100 is large, 3^200 / (y+3) is small positive fraction (< 1).
    -- So floor(y^200 / (y+3)) = Q(y).
    -- We need Q(y) mod 10.
    -- Q(y) = y^199 - 3*y^198 + ... + (-3)^199.
    -- Since y = 10^100, y is divisible by 10. So y^k for k>=1 is 0 mod 10.
    -- The only term in Q(y) not divisible by 10 is the constant term (-3)^199.
    -- So Q(y) == (-3)^199 (mod 10).
    -- (-3)^199 = -(3^199).
    -- 3^199 mod 10: Cycle of 3^k mod 10 is 3, 9, 7, 1. Length 4.
    -- 199 = 4*49 + 3. So 3^199 == 3^3 == 27 == 7 (mod 10).
    -- So Q(y) == -7 == 3 (mod 10).
    -- Formalizing the value of Q(y) as an integer and showing it equals the floor.
    -- Let's define the polynomial sum.
    repeat' rw [h_expr]; norm_num [y, h_y_pow]

  exact h_main
