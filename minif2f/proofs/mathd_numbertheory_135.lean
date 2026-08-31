import Mathlib
open BigOperators Real Nat Topology Rat

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)
/-- Let $n = 3^{17} + 3^{10}$. It is known that $11$ divides into $n+1$. If $n$ can be written in base $10$ as $ABCACCBAB$, where $A,B,C$ are distinct digits such that $A$ and $C$ are odd and $B$ is not divisible by $3$, find $100A + 10B + C$. Show that it is 129.-/

theorem mathd_numbertheory_135 (n A B C : ℕ) (h₀ : n = 3 ^ 17 + 3 ^ 10) (h₁ : 11 ∣ n + 1)
    (h₂ : [A, B, C].Pairwise (· ≠ ·)) (h₃ : {A, B, C} ⊂ Finset.Icc 0 9) (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬3 ∣ B) (h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]) :
    100 * A + 10 * B + C = 129 := by

  subst h₀
  simp_all only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self, and_true, reducePow, reduceAdd, reduceDvd, reduceLeDiff, ofNat_pos, digits_of_two_le_of_pos, reduceMod, reduceDiv, zero_lt_one, one_mod, digits_zero, List.cons.injEq, _root_.and_self_left]
  (linarith)
