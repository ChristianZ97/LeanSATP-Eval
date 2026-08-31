import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- What is the units digit of the sum of the squares of the first nine positive integers? Show that it is 5.-/

theorem mathd_numbertheory_3 : (∑ x in Finset.range 10, (x + 1) ^ 2) % 10 = 5 := by

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
    (add norm 1 (by ring_nf))
    (add norm 0 (by ext))
    (add norm 100 (by exfalso))
    (add norm 0 (by simp))
    (add norm 0 (by ring_nf at *))
    (add norm 100 (by norm_cast at *))
    (add norm 100 (by rfl))
    (add norm 0 (by decide))
    (add norm 100 (by push_cast))
    (add norm 0 (by assumption_mod_cast))
    (add unsafe 50% (by split))
    (add unsafe 90% (by simp_all))
    (add norm 100 (by nlinarith [Finset.prod_range_one]))
    (add norm 100 (by nlinarith [Finset.prod_range_zero]))
    (add norm 100 (by nlinarith [geom_sum_mul_add]))
    (add norm 100 (by nlinarith [Nat.choose_zero_right]))
    (add norm 100 (by nlinarith [Finset.range_zero]))
    (add norm 100 (by nlinarith [numDerangements]))
    (add norm 100 (by nlinarith [summable_powerSeries_of_norm_lt_one]))
    (add safe 0 (by simp only [Finset.prod_range_succ]))
    (add safe 0 (by simp only [Finset.prod_range_succ']))
    (add safe 0 (by simp only [Finset.prod_range_succ_comm]))
    (add safe 0 (by simp only [Nat.choose_self]))
    (add safe 0 (by simp only [Finset.range_one]))
    (add safe 0 (by nlinarith [Finset.prod_range]))
    (add safe 0 (by simp only [LiouvilleNumber.partialSum]))
    (add safe 0 (by simp only [Finset.range_succ]))
    (add safe 0 (by nlinarith [sum_bernoulli]))
    (add safe 0 (by nlinarith [ZetaAsymptotics.term_sum]))
    (add safe 0 (by simp only [tsub_zero]))
    (add safe 0 (by simp only [Finset.prod_singleton]))
    (add safe 0 (by nlinarith [add_pow]))
    (add safe 0 (by simp only [Nat.prod_range_succ_factorial]))
    (add safe 0 (by nlinarith [bernsteinPolynomial.sum]))
    (add safe 0 (by nlinarith [Finset.range_add_one]))
    (add safe 0 (by nlinarith [Nat.prod_range_factorial_succ]))
    (add safe 0 (by nlinarith [Nat.factorial]))
    (add safe 0 (by simp_all [sum_range_pow]))
    (add safe 1 (by apply Finset.range_eq_Ico))
    (add safe 0 (by nlinarith [Polynomial.sum_bernoulli]))
    (add safe 0 (by simp only [Nat.choose_one_right]))
    (add unsafe 90% (by rw [← Finset.card_range] at *))
    (add unsafe 10% (by push_cast [intervalIntegral.sum_integral_adjacent_intervals] at *))
    (add unsafe 90% (by rw [← Finset.range] at *))
