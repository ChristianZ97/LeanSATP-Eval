import Mathlib
open BigOperators Real Nat Topology Rat
/-- Let $n = 3^{17} + 3^{10}$. It is known that $11$ divides into $n+1$. If $n$ can be written in base $10$ as $ABCACCBAB$, where $A,B,C$ are distinct digits such that $A$ and $C$ are odd and $B$ is not divisible by $3$, find $100A + 10B + C$. Show that it is 129.-/

theorem mathd_numbertheory_135 (n A B C : ℕ) (h₀ : n = 3 ^ 17 + 3 ^ 10) (h₁ : 11 ∣ n + 1)
    (h₂ : [A, B, C].Pairwise (· ≠ ·)) (h₃ : {A, B, C} ⊂ Finset.Icc 0 9) (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬3 ∣ B) (h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]) :
    100 * A + 10 * B + C = 129 := by

    subst h₀
    simp_all only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self, and_true, reducePow, reduceAdd, reduceLeDiff,
      ofNat_pos, digits_of_two_le_of_pos, reduceMod, reduceDiv, lt_one_iff, pos_of_gt, one_mod, digits_zero,
      List.cons.injEq, and_self_left]
    obtain ⟨left, right⟩ := h₂
    obtain ⟨left_1, right_1⟩ := h₄
    obtain ⟨left_2, right_2⟩ := h₆
    obtain ⟨left, right_3⟩ := left
    obtain ⟨left_3, right_2⟩ := right_2
    obtain ⟨left_4, right_2⟩ := right_2
    obtain ⟨left_5, right_2⟩ := right_2
    obtain ⟨left_6, right_2⟩ := right_2
    obtain ⟨left_7, right_2⟩ := right_2
    obtain ⟨left_8, right_2⟩ := right_2
    subst left_7 left_3 left_2
    simp_all only [odd_one, OfNat.one_ne_ofNat, not_false_eq_true, reduceEqDiff, mul_one, reduceMul, reduceAdd]