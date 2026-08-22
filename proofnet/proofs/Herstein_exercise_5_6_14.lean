
import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  -- Step 1: Define the polynomial f(X) = X^{p^n} - X
  let f : Polynomial F := X ^ m - X

  -- Step 2 & 3: Compute the derivative f'(X) = p^n * X^{p^n - 1} - 1
  have h_deriv_def : f.derivative = (C (m • (1 : F))) * X ^ (m - 1) - C (1 : F) := by
    clear * - hm hp hn
    simp [f, derivative_X_pow]

  -- Step 4 & 5 & 6: In characteristic p, p^n * 1_F = 0_F because p * 1_F = 0_F and n > 0
  have h_char_zero : (m : F) = 0 := by
    clear * - hm hp hn
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [CharP.cast_eq_zero_iff]))
      (add norm 0 (by grind only [Nat.Prime.ne_zero]))
      (add norm 0 (by grind only [CharP.cast_eq_zero]))
      (add norm 0 (by rw [Nat.cast_pow]))
      (add norm 0 (by rw [ZMod.natCast_self]))
      (add norm 0 (by grind only [ZMod.natCast_zmod_eq_zero_iff_dvd]))
      (add norm 0 (by grind only [PerfectClosure.natCast]))
      (add norm 0 (by grind only [PerfectClosure.natCast_eq_iff]))
      (add norm 0 (by grind only [Nat.Prime.pos]))
      (add norm 0 (by grind only [sub_pow_char]))
      (add norm 0 (by grind only [legendreSym.eq_zero_iff]))
      (add norm 0 (by rw [ZMod.natCast_zmod_val]))
      (add norm 0 (by grind only [MulChar.pow_apply']))
      (add norm 0 (by grind only [MulChar.IsQuadratic.pow_char]))
      (add norm 0 (by grind only [AddChar.pow_apply]))
      (add norm 0 (by grind only [zero_pow]))
      (add norm 0 (by grind only [PadicInt.unitCoeff_spec]))
      (add norm 0 (by rw [Nat.cast_npow]))
      (add norm 0 (by grind only [sub_pow_char_of_commute]))
      (add norm 0 (by grind only [Nat.cast_card_eq_zero]))
      (add norm 0 (by grind only [LucasLehmer.ω_pow_eq_neg_one]))
      (add norm 0 (by rw [PadicInt.coe_pow]))
      (add norm 0 (by grind only [irrational_nrt_of_notint_nrt]))
      (add norm 0 (by grind only [ZMod.eq_zero_iff_even]))
      (add norm 0 (by grind only [ZMod.val]))
      (add norm 0 (by grind only [ZMod.val_cast_of_lt]))
      (add norm 0 (by grind only [Nat.cast_ne_zero]))
      (add norm 0 (by grind only [Nat.Prime.one_lt]))
      (add norm 0 (by grind only [sub_pow_char_pow]))
      (add norm 0 (by grind only [Polynomial.cyclotomic_mul_prime_pow_eq]))
      (add norm 0 (by grind only [PadicInt.nthHom]))
      (add norm 0 (by grind only [LucasLehmer.s]))

  -- Step 7: Therefore, the term p^n * X^{p^n - 1} vanishes
  have h_first_term_zero : (C (m • (1 : F))) * X ^ (m - 1) = 0 := by
    clear * - h_char_zero
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
      })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add norm 1 (by norm_num [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 10% (by exfalso))
      (add norm 0 (by grind only [MulZeroClass]))
      (add norm 0 (by grind only [zero_pow]))
      (add norm 0 (by grind only [Polynomial.derivative_C]))
      (add norm 0 (by grind only [Polynomial.C_0]))
      (add norm 0 (by grind only [Polynomial.C_pow]))
      (add norm 0 (by grind only [Derivation.leibniz_pow]))
      (add norm 0 (by grind only [Polynomial.derivative_pow]))
      (add norm 0 (by grind only [Polynomial.hasseDeriv_C]))
      (add norm 0 (by grind only [Nat.cast_zero]))
      (add norm 0 (by grind only [MvPolynomial.C_mul']))
      (add norm 0 (by grind only [LaurentPolynomial.T_zero]))
      (add norm 0 (by grind only [Polynomial.derivation_C]))
      (add norm 0 (by grind only [Polynomial.smul_X]))
      (add norm 0 (by grind only [FiniteField.cast_card_eq_zero]))
      (add norm 0 (by grind only [Polynomial.C_eq_natCast]))
      (add norm 0 (by grind only [Polynomial.C_1]))
      (add norm 0 (by grind only [FiniteField.pow_card]))
      (add norm 0 (by rw [ZMod.natCast_self]))
      (add norm 0 (by grind only [Polynomial.C_mul']))
      (add norm 0 (by grind only [CharP.cast_eq_zero]))
      (add norm 0 (by grind only [Polynomial.C_mul]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero']))
      (add norm 0 (by grind only [MvPolynomial.C_eq_coe_nat]))
      (add norm 0 (by grind only [legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero]))
      (add norm 0 (by grind only [Cubic.of_b_eq_zero]))
      (add norm 0 (by grind only [LucasLehmer.s]))
      (add norm 0 (by grind only [Polynomial.divX_C]))
      (add norm 0 (by grind only [MulChar.pow_apply']))
      (add norm 0 (by grind only [Polynomial.smul_C]))
      (add norm 0 (by grind only [WeierstrassCurve.ψ_zero]))
      (add norm 0 (by grind only [Polynomial.expand_C]))
      (add norm 0 (by grind only [MvPolynomial.pderiv_C]))

  -- Step 8: Thus, f'(X) = -1
  have h_deriv_eq_neg_one : f.derivative = -C (1 : F) := by
    clear * - h_deriv_def h_first_term_zero
    aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
      useDefaultSimpSet := false
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [Polynomial.derivative_C]))
      (add norm 0 (by grind only [Polynomial.derivative_sub]))
      (add norm 0 (by grind only [Polynomial.C_sub]))
      (add norm 0 (by grind only [Polynomial.expand_C]))
      (add norm 0 (by grind only [Polynomial.derivative_pow]))
      (add norm 0 (by grind only [galois_poly_separable]))
      (add norm 0 (by grind only [Polynomial.C_1]))
      (add norm 0 (by grind only [Polynomial.X]))
      (add norm 0 (by grind only [Polynomial.X_sub_C_ne_zero]))
      (add norm 0 (by grind only [Polynomial.derivative_X]))
      (add norm 0 (by grind only [Polynomial.isCoprime_X_sub_C_of_isUnit_sub]))
      (add norm 0 (by grind only [AdjoinRoot.root_isInv]))
      (add norm 0 (by grind only [Polynomial.X_pow_sub_C_ne_zero]))
      (add norm 0 (by grind only [Polynomial.C_pow]))
      (add norm 0 (by grind only [Polynomial.modByMonic_X_sub_C_eq_C_eval]))
      (add norm 0 (by grind only [Polynomial.C]))
      (add norm 0 (by grind only [Polynomial.X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic]))
      (add norm 0 (by grind only [FiniteField.X_pow_card_sub_X_ne_zero]))
      (add norm 0 (by grind only [Polynomial.derivative_one]))
      (add norm 0 (by grind only [Polynomial.C_neg]))
      (add norm 0 (by grind only [Polynomial.separable_X_sub_C]))
      (add norm 0 (by grind only [Polynomial.C_inj]))
      (add norm 0 (by grind only [Polynomial.separable_X_pow_sub_C]))
      (add norm 0 (by grind only [Cubic.C_mul_prod_X_sub_C_eq]))
      (add norm 0 (by grind only [Polynomial.separable_X_pow_sub_C_unit]))
      (add norm 0 (by grind only [Polynomial.derivative_X_pow]))
      (add norm 0 (by grind only [Polynomial.expand_eq_C]))
      (add norm 0 (by grind only [Polynomial.derivative_X_sub_C]))
      (add norm 0 (by grind only [Polynomial.derivative_X_sub_C_pow]))
      (add norm 0 (by grind only [Polynomial.degree_X_pow_sub_C]))
      (add norm 0 (by grind only [Polynomial.derivative]))
      (add norm 0 (by grind only [Polynomial.C_mul]))

  -- Step 9 & 10: gcd(f, f') = gcd(f, -1) = 1
  have h_gcd_one : IsCoprime f f.derivative := by
    clear * - h_deriv_eq_neg_one
    rw [h_deriv_eq_neg_one]
    apply isCoprime_one_right.neg_right

  -- Step 11: A polynomial is separable iff it is coprime to its derivative
  have h_separable : f.Separable := by
    clear * - h_gcd_one
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableSimp := false
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
      (add safe 100 (by omega))
      (add safe 100 (by push_neg))
      (add safe 100 (by interval_cases))
      (add safe 0 (by norm_num [*] at *))
      (add safe 100 (by norm_cast at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Polynomial.separable_def]))
      (add norm 0 (by grind only [Polynomial.isCoprime_X_sub_C_of_isUnit_sub]))
      (add norm 0 (by grind only [galois_poly_separable]))
      (add norm 0 (by grind only [X_pow_sub_C_irreducible_of_prime]))
      (add norm 0 (by grind only [Polynomial.Separable]))
      (add norm 0 (by grind only [Polynomial.separable_X_pow_sub_C_unit]))
      (add norm 0 (by grind only [EuclideanDomain.dvd_or_coprime]))
      (add norm 0 (by grind only [Polynomial.separable_X_pow_sub_C]))
      (add norm 0 (by grind only [Polynomial.X_pow_sub_X_sub_one_irreducible]))
      (add norm 0 (by grind only [Polynomial.separable_X_sub_C]))
      (add norm 0 (by grind only [ne_zero_of_irreducible_X_pow_sub_C]))
      (add norm 0 (by grind only [Polynomial.irreducible_X_sub_C]))
      (add norm 0 (by grind only [ne_zero_of_irreducible_X_pow_sub_C']))
      (add norm 0 (by grind only [PerfectField]))
      (add norm 0 (by grind only [Polynomial.X_pow_sub_C_ne_zero]))
      (add norm 0 (by grind only [Polynomial.irreducible_X]))
      (add norm 0 (by grind only [Polynomial.X_pow_sub_X_sub_one_irreducible_rat]))
      (add norm 0 (by grind only [Polynomial.degree_X_pow_sub_C]))
      (add norm 0 (by grind only [Polynomial.derivative_sub]))
      (add norm 0 (by grind only [Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero]))
      (add norm 0 (by grind only [FiniteField.X_pow_card_sub_X_ne_zero]))
      (add norm 0 (by grind only [dvd_or_coprime]))
      (add norm 0 (by grind only [Polynomial.expand]))
      (add norm 0 (by grind only [Polynomial.isUnit_iff_degree_eq_zero]))
      (add norm 0 (by grind only [Polynomial.X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic]))
      (add norm 0 (by grind only [Polynomial.degree_X_sub_C]))
      (add norm 0 (by grind only [Polynomial.irreducible_of_degree_eq_one]))
      (add norm 0 (by grind only [not_irreducible_expand]))
      (add norm 0 (by grind only [Polynomial.X]))
      (add norm 0 (by grind only [Polynomial.C]))
      (add norm 0 (by grind only [Polynomial.not_irreducible_C]))
      (add norm 0 (by grind only [X_pow_sub_C_irreducible_of_odd]))

  exact h_separable
