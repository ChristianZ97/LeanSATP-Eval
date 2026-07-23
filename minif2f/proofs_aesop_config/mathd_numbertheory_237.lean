import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- What is the modulo $6$ remainder of the sum $1+2+3+4+\dots+98+99+100?$ Show that it is 4.-/

theorem mathd_numbertheory_237 : (∑ k in Finset.range 101, k) % 6 = 4 := by

  aesop (config := {
    maxRuleApplicationDepth := 10
    maxNormIterations := 520
    maxGoals := 1024
    useDefaultSimpSet := false
    })
    (add norm 100 (by ring))
    (add norm 100 (by field_simp))
    (add norm 100 (by norm_num))
    (add norm 100 (by norm_cast))
    (add norm 100 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 100 (by abel))
    (add norm 100 (by zify))
    (add norm 100 (by gcongr))
    (add norm 0 (by bound))
    (add norm 0 (by interval_cases))
    (add norm 0 (by ext))
    (add norm 100 (by exfalso))
    (add norm 0 (by simp))
    (add norm 0 (by ring_nf at *))
    (add norm 100 (by norm_cast at *))
    (add norm 100 (by rfl))
    (add norm 0 (by decide))
    (add norm 100 (by push_cast))
    (add norm 0 (by assumption_mod_cast))
    (add unsafe 10% (by ring_nf))
    (add unsafe 50% (by split))
    (add unsafe 90% (by simp_all))
    (add norm 100 (by nlinarith [Finset.prod_range_one]))
    (add norm 100 (by nlinarith [Finset.prod_range_zero]))
    (add norm 100 (by nlinarith [intervalIntegral.sum_integral_adjacent_intervals]))
    (add norm 0 (by grind only [geom_sum_mul_add]))
    (add norm 100 (by nlinarith [summable_powerSeries_of_norm_lt_one]))
    (add norm 100 (by nlinarith [numDerangements]))
    (add norm 100 (by nlinarith [Finset.range_zero]))
    (add norm 100 (by nlinarith [Nat.choose_zero_right]))
    (add safe 0 (by simp only [Finset.prod_range_succ]))
    (add safe 0 (by simp only [Finset.prod_range_succ']))
    (add safe 0 (by simp only [Finset.prod_range_succ_comm]))
    (add safe 0 (by nlinarith [Finset.prod_range]))
    (add safe 0 (by simp only [Finset.range_one]))
    (add safe 0 (by nlinarith [sum_bernoulli]))
    (add safe 0 (by simp only [Nat.choose_self]))
    (add safe 0 (by nlinarith [ZetaAsymptotics.term_sum]))
    (add safe 0 (by simp only [LiouvilleNumber.partialSum]))
    (add safe 0 (by nlinarith [bernsteinPolynomial.sum]))
    (add safe 0 (by nlinarith [Finset.range_add_one]))
    (add safe 0 (by simp only [Finset.range_succ]))
    (add safe 0 (by nlinarith [add_pow]))
    (add safe 0 (by simp_all [Finset.prod_range_succ_div_prod]))
    (add safe 0 (by simp_all [sum_range_pow]))
    (add safe 0 (by nlinarith [Polynomial.sum_bernoulli]))
    (add safe 0 (by simp_all [Finset.prod_range_induction]))
    (add safe 0 (by nlinarith [Fin.prod_univ_eq_prod_range]))
    (add safe 0 (by simp only [Nat.prod_range_succ_factorial]))
    (add safe 0 (by simp only [Finset.prod_singleton]))
    (add safe 0 (by nlinarith [Nat.prod_range_factorial_succ]))
    (add safe 1 (by apply Finset.prod_range_mul_prod_Ico))
    (add unsafe 90% (by rw [← Finset.card_range] at *))
    (add unsafe 90% (by rw [← Finset.range] at *))
