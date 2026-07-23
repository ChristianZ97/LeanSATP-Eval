import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- Determine the modulo 4 remainder of the following sum: $$ 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12. $$ Show that it is 2.-/

theorem mathd_numbertheory_239 : (∑ k in Finset.Icc 1 12, k) % 4 = 2 := by

  aesop (config := {
    maxRuleApplicationDepth := 10
    maxNormIterations := 520
    maxGoals := 64
    useSimpAll := false
    useDefaultSimpSet := false
    }) (rule_sets := [-builtin])
    (add norm 100 (by ring))
    (add norm 100 (by field_simp))
    (add norm 100 (by norm_num))
    (add norm 100 (by norm_cast))
    (add norm 0 (by nlinarith))
    (add norm 100 (by positivity))
    (add norm 0 (by omega))
    (add norm 100 (by abel))
    (add norm 100 (by zify))
    (add norm 0 (by gcongr))
    (add norm 0 (by bound))
    (add norm 0 (by interval_cases))
    (add norm 0 (by ring_nf))
    (add norm 0 (by ext))
    (add norm 100 (by exfalso))
    (add norm 0 (by simp))
    (add norm 0 (by simp_all))
    (add norm 0 (by ring_nf at *))
    (add norm 100 (by norm_cast at *))
    (add norm 100 (by rfl))
    (add norm 100 (by push_cast))
    (add safe 0 (by linarith))
    (add unsafe 50% (by norm_num [*] at *))
    (add norm 0 (by apply Finset.Icc))
    (add norm 0 (by rw [← Finset.prod_const]))
    (add norm 1 (by simp_all [Finset.card_fin]))
    (add norm 0 (by apply Nat.card_Icc))
    (add norm 100 (by simp only [mul_assoc] at *))
    (add norm 0 (by rw [← Finset.prod_mul_distrib]))
    (add safe 0 (by simp only [Nat.prod_Icc_factorial]))
    (add safe 0 (by nlinarith [Nat.det_vandermonde_id_eq_superFactorial]))
    (add safe 100 (by simp_rw [mul_comm]))
    (add safe 0 (by nlinarith [Nat.cast_ofNat]))
    (add unsafe 10% (by push_cast [Finset.prod_singleton] at *))
    (add unsafe 10% (by push_cast [harmonic_eq_sum_Icc] at *))
    (add unsafe 10% (by push_cast [Finset.prod] at *))
    (add unsafe 10% (by push_cast [Finset.prod_const_one] at *))
    (add unsafe 10% (by push_cast [Finset.mul_sum] at *))
    (add unsafe 10% (by push_cast [Finset.prod_empty] at *))
    (add unsafe 10% (by push_cast [Nat.Ico_zero_eq_range] at *))
    (add unsafe 10% (by push_cast [Finset.card_range] at *))
    (add unsafe 10% (by push_cast [PicardLindelof.proj_coe] at *))
    (add unsafe 10% (by push_cast [Nat.cast_sum] at *))
    (add unsafe 10% (by push_cast [Finset.range_eq_Ico] at *))
    (add unsafe 10% (by push_cast [two_mul] at *))
    (add unsafe 10% (by push_cast [Finset.single_le_prod'] at *))
    (add unsafe 10% (by push_cast [ZMod.eisenstein_lemma_aux₁] at *))
    (add unsafe 10% (by push_cast [Finset.prod_range_succ] at *))
    (add unsafe 10% (by push_cast [Finset.prod_le_prod'] at *))
    (add unsafe 10% (by push_cast [Finset.prod_Ico_add] at *))
    (add unsafe 10% (by push_cast [Finset.prod_range] at *))
    (add unsafe 10% (by push_cast [Finset.prod_range_mul_prod_Ico] at *))
    (add unsafe 10% (by push_cast [Finset.prod_Ico_consecutive] at *))
    (add unsafe 10% (by push_cast [Finset.prod_range_succ'] at *))
    (add unsafe 10% (by push_cast [Finset.prod_Ico_add'] at *))
