import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- What is the sum of the units digits of all the multiples of $3$ between $0$ and $50$? Show that it is 78.-/

theorem mathd_numbertheory_447 :
    (∑ k in Finset.filter (fun x => 3 ∣ x) (Finset.Icc 1 49), k % 10) = 78 := by

  aesop (config := {
    maxRuleApplicationDepth := 10
    maxNormIterations := 520
    useSimpAll := false
    enableUnfold := false
    useDefaultSimpSet := false
    }) (rule_sets := [-builtin])
    (add norm 100 (by ring))
    (add norm 100 (by field_simp))
    (add norm 100 (by norm_num))
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 100 (by abel))
    (add norm 100 (by zify))
    (add norm 100 (by gcongr))
    (add norm 0 (by bound))
    (add norm 0 (by ext))
    (add norm 100 (by exfalso))
    (add norm 0 (by ring_nf at *))
    (add norm 100 (by norm_num [*] at *))
    (add norm 100 (by norm_cast at *))
    (add norm 100 (by rfl))
    (add norm 100 (by push_cast))
    (add norm 100 (by assumption_mod_cast))
    (add safe 0 (by ring_nf))
    (add unsafe 90% (by simp_all))
    (add norm 0 (by apply Finset.Icc))
    (add norm 0 (by apply Nat.card_Icc))
    (add norm 0 (by apply Pi.card_Icc))
    (add norm 0 (by apply Int.card_Icc))
    (add norm 0 (by rw [← Finset.card_range]))
    (add norm 0 (by apply PNat.card_Icc))
    (add norm 0 (by rw [← Set.projIcc_of_mem]))
    (add norm 0 (by apply Fin.card_Icc))
    (add norm 1 (by simp_all [Nat.cast_sum]))
    (add safe 0 (by simp only [Nat.prod_Icc_factorial]))
    (add safe 1 (by apply primorial))
    (add safe 0 (by simp only [Finset.prod_Icc_succ_top]))
    (add safe 0 (by nlinarith [Fin.Icc_eq_finset_subtype]))
    (add safe 1 (by rw [Nat.Prime.multiplicity_choose_aux]))
    (add safe 1 (by apply Finset.prod_empty))
    (add unsafe 10% (by push_cast [harmonic_eq_sum_Icc] at *))
    (add unsafe 10% (by push_cast [Nat.Ico_zero_eq_range] at *))
    (add unsafe 10% (by push_cast [Finset.Icc_eq_empty_of_lt] at *))
    (add unsafe 10% (by push_cast [PicardLindelof.proj_coe] at *))
    (add unsafe 10% (by push_cast [Finset.Icc_neg_mono] at *))
    (add unsafe 10% (by push_cast [Finset.range_eq_Ico] at *))
    (add unsafe 10% (by push_cast [Finset.Icc_self] at *))
    (add unsafe 10% (by push_cast [Finset.prod_Ico_consecutive] at *))
    (add unsafe 10% (by push_cast [Finset.Icc_eq_cons_Ico] at *))
    (add unsafe 10% (by push_cast [Finset.prod_Ico_add] at *))
    (add unsafe 10% (by push_cast [Finset.prod_Ico_add'] at *))
    (add unsafe 10% (by push_cast [MonotoneOn.sum_le_integral_Ico] at *))
    (add unsafe 10% (by push_cast [Finset.prod_range_mul_prod_Ico] at *))
    (add unsafe 10% (by push_cast [Finset.prod_singleton] at *))
    (add unsafe 10% (by push_cast [eVariationOn.sum_le_of_monotoneOn_Icc] at *))
    (add unsafe 10% (by push_cast [Finset.Ico_self] at *))
    (add unsafe 10% (by push_cast [Finset.Ico_insert_right] at *))
