import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- How many integers between 15 and 85 are divisible by 20? Show that it is 4.-/

theorem mathd_numbertheory_12 :
    Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by

  aesop (config := {
    maxRuleApplicationDepth := 20
    maxNormIterations := 520
    useSimpAll := false
    enableUnfold := false
    useDefaultSimpSet := false
    }) (rule_sets := [-builtin])
    (add norm 1 (by ring))
    (add norm 100 (by norm_num))
    (add norm 100 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 0 (by gcongr))
    (add norm 0 (by bound))
    (add norm 0 (by ext))
    (add norm 0 (by simp))
    (add norm 1 (by simp_all))
    (add norm 0 (by ring_nf at *))
    (add norm 100 (by rfl))
    (add norm 100 (by push_cast))
    (add safe 1 (by zify))
    (add safe 0 (by ring_nf))
    (add safe 0 (by exfalso))
    (add unsafe 50% (by norm_cast))
    (add unsafe 50% (by abel))
    (add unsafe 50% (by norm_num [*] at *))
    (add unsafe 50% (by norm_cast at *))
    (add norm 0 (by apply Nat.card_Icc))
    (add norm 0 (by apply PNat.card_Icc))
    (add norm 0 (by apply Fin.card_Icc))
    (add norm 0 (by apply Pi.card_Icc))
    (add norm 0 (by apply Int.card_Icc))
    (add norm 100 (by rw [Finset.card_singleton]))
    (add norm 0 (by apply Int.card_Icc_of_le))
    (add norm 0 (by apply Multiset.card_Icc))
    (add norm 0 (by apply Sigma.card_Icc))
    (add norm 100 (by rw [Finset.card_one]))
    (add norm 100 (by rw [Finset.card_Icc_finset]))
    (add norm 0 (by apply Finsupp.card_Icc))
    (add norm 0 (by apply Prod.card_Icc))
    (add norm 0 (by apply Finset.Icc))
    (add norm 100 (by rw [Finset.card_eq_sum_ones]))
    (add norm 0 (by apply DFinsupp.card_Icc))
    (add norm 100 (by rw [Finset.cast_card]))
    (add norm 0 (by apply Int.card_fintype_Icc))
    (add norm 0 (by rw [← Nat.card_fintypeIcc]))
    (add norm 1 (by simp_all [SimpleGraph.dart_card_eq_twice_card_edges]))
    (add norm 100 (by rw [Finset.card]))
    (add norm 100 (by rw [Finset.sum_const_nat]))
    (add norm 1 (by simp_all [Finset.card_pair]))
    (add norm 100 (by rw [Finset.card_powerset]))
    (add norm 100 (by rw [Finset.card_powersetCard]))
    (add norm 100 (by rw [Fin.card_Ioi]))
    (add norm 100 (by rw [Finset.card_singleton_mul]))
    (add safe 1 (by rw [Finset.card_Ico_eq_card_Icc_sub_one]))
    (add safe 1 (by rw [← Nat.card_Ico] at *))
    (add safe 1 (by rw [Set.toFinset_Icc]))
    (add unsafe 50% (by simp_rw [PNat.card_fintype_Icc]))
    (add unsafe 50% (by push_cast [Finset.card_map] at *))
