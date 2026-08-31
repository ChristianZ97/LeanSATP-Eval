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

  aesop (config := {
    maxRuleApplicationDepth := 10
    maxNormIterations := 520
    maxGoals := 1024
    })
    (add norm 100 (by ring))
    (add norm 100 (by field_simp))
    (add norm 100 (by norm_num))
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 100 (by abel))
    (add norm 100 (by zify))
    (add norm 100 (by bound))
    (add norm 100 (by interval_cases))
    (add norm 100 (by ext))
    (add norm 100 (by split))
    (add norm 100 (by exfalso))
    (add norm 100 (by ring_nf at *))
    (add norm 1 (by field_simp [*] at *))
    (add norm 100 (by norm_num [*] at *))
    (add norm 100 (by norm_cast at *))
    (add norm 100 (by rfl))
    (add norm 100 (by push_cast))
    (add norm 100 (by assumption_mod_cast))
    (add safe 1 (by ring_nf))
    (add unsafe 90% (by simp_all))
    (add norm 1 (by norm_num [mul_right_comm] at *))
    (add norm 100 (by simp only [mul_assoc] at *))
    (add norm 0 (by grind only [Nat.div_add_mod]))
    (add norm 0 (by simp [Zsqrtd.SqLe] at *))
    (add norm 0 (by simp [Nat.succ_mul] at *))
    (add norm 0 (by grind only [Pell.eq_of_xn_modEq_lem2]))
    (add norm 0 (by grind only [Nat.mod_add_div]))
    (add norm 0 (by grind only [Nat.add_sub_of_le]))
    (add norm 0 (by simp [Zsqrtd.sqLe_smul] at *))
    (add norm 1 (by simp_all [two_mul]))
    (add norm 0 (by grind only [Nat.add_sub_assoc]))
    (add norm 0 (by simp [Nat.succ_mul_centralBinom_succ] at *))
    (add norm 0 (by simp [Nat.mul_one] at *))
    (add norm 0 (by simp [Nat.left_distrib] at *))
    (add norm 0 (by simp [Nat.mul_add] at *))
    (add norm 0 (by grind only [tsub_add_cancel_of_le]))
    (add norm 1 (by simp_all [Eq.symm]))
    (add norm 0 (by simp [Nat.le_add_left] at *))
    (add norm 0 (by grind only [Pell.pellZd]))
    (add norm 0 (by grind only [Nat.add_le_add]))
    (add norm 0 (by grind only [Nat.add_sub_cancel']))
    (add norm 0 (by simp [Nat.mul_le_mul_left] at *))
    (add norm 0 (by simp [Nat.mul_succ] at *))
    (add safe 0 (by norm_num [mul_add_mul] at *))
    (add safe 100 (by grind only [Zsqrtd.not_divides_sq]))
    (add safe 0 (by norm_num [Pell.isPell_norm] at *))
    (add unsafe 10% (by push_cast [mul_left_comm] at *))
    (add unsafe 10% (by field_simp [mul_comm] at *))
    (add unsafe 50% (by simp_rw [Pell.d]))
    (add unsafe 90% (by simp [Nat.div_add_mod'] at *))
    (add unsafe 50% (by simp_rw [Pell.dz_val]))
    (add unsafe 10% (by field_simp [Pell.xn] at *))
