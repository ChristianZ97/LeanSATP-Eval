/- Release note: the second gap closes via `native_decide` (a 9000-element
   digit-filter cardinality check, infeasible for kernel `decide`). This file
   depends on Lean.ofReduceBool / Lean.trustCompiler beyond the standard trio;
   see README. -/
import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem amc12a_2020_p4 (S : Finset ℕ)
  (h₀ : ∀ n : ℕ, n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
  S.card = 100 := by
  have h_arithmetic : (4 : ℕ) * 5 * 5 * 1 = 100 := by
    clear * -
    aesop (config := {
      maxRuleApplicationDepth := 10
      maxNormIterations := 520
      useSimpAll := false
      enableUnfold := false
      }) (rule_sets := [-builtin])
      (add norm 100 (by ring))
      (add norm 100 (by field_simp))
      (add norm 100 (by norm_num))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 100 (by abel))
      (add norm 100 (by zify))
      (add norm 100 (by gcongr))
      (add norm 0 (by bound))
      (add norm 100 (by interval_cases))
      (add norm 100 (by ext))
      (add norm 100 (by split))
      (add norm 100 (by exfalso))
      (add norm 100 (by simp))
      (add norm 100 (by ring_nf at *))
      (add norm 100 (by norm_num [*] at *))
      (add norm 100 (by norm_cast at *))
      (add norm 100 (by rfl))
      (add norm 100 (by push_cast))
      (add norm 100 (by assumption_mod_cast))
      (add safe 1 (by ring_nf))
      (add safe 0 (by simp_all))
      (add safe 0 (by field_simp [*] at *))
      (add unsafe 50% (by norm_cast))
      (add norm 100 (by simp only [mul_assoc] at *))
      (add norm 100 (by simp only [mul_comm] at *))
      (add norm 100 (by simp only [mul_one] at *))
      (add norm 100 (by simp only [one_mul] at *))
      (add norm 0 (by grind only [Pell.d]))
      (add safe 1 (by rw [QuaternionAlgebra.mul_imI]))
      (add unsafe 10% (by push_cast [mul_left_comm] at *))
      (add unsafe 10% (by push_cast [mul_right_comm] at *))
      (add unsafe 10% (by push_cast [mul_add_mul] at *))
      (add unsafe 90% (by grind only [mul_self]))
      (add unsafe 10% (by push_cast [mul_right_inj'] at *))
      (add unsafe 10% (by push_cast [mul_left_cancel₀] at *))
      (add unsafe 90% (by norm_num [Quaternion.coe_commutes] at *))
      (add unsafe 50% (by solve_by_elim [mul_mul_mul_comm]))
      (add unsafe 90% (by grind only [Int.sq_add_sq_of_two_mul_sq_add_sq]))
      (add unsafe 10% (by push_cast [Pell.isPell_norm] at *))
      (add unsafe 50% (by simp only [sq_add_mul_sq_mul_sq_add_mul_sq]))
      (add unsafe 10% (by push_cast [mul_lt_mul_left] at *))
      (add unsafe 10% (by push_cast [two_mul] at *))
      (add unsafe 90% (by norm_num [QuaternionAlgebra.coe_commutes] at *))
      (add unsafe 10% (by push_cast [Quaternion.self_add_star] at *))
      (add unsafe 10% (by push_cast [FractionalIdeal.dual_mul_self] at *))
      (add unsafe 90% (by grind only [goldConj_sq]))
      (add unsafe 50% (by simp only [sq_add_sq_mul_sq_add_sq]))
      (add unsafe 10% (by push_cast [QuaternionGroup.a_mul_a] at *))
      (add unsafe 10% (by push_cast [mul_div_cancel₀] at *))
      (add unsafe 50% (by simp only [Int.sq_eq_one_of_sq_le_three]))
      (add unsafe 10% (by push_cast [mul_le_mul_left] at *))
      (add unsafe 10% (by push_cast [ArithmeticFunction.mul_apply_one] at *))
      (add unsafe 10% (by push_cast [QuaternionAlgebra.self_add_star] at *))
      (add unsafe 10% (by push_cast [mul_lt_mul_iff_left] at *))
      (add unsafe 50% (by unfold QuaternionAlgebra.Basis.k_mul_j))

  set S_def := h₀
  convert_to ((Finset.Icc 1000 9999).filter fun n => (∀ d ∈ Nat.digits 10 n, Even d) ∧ 5 ∣ n).card = 100
  · congr 1 <;> ext n <;> aesop
  · native_decide <;> unfold Finset.card

