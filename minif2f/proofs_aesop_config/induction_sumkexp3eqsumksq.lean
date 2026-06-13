import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem induction_sumkexp3eqsumksq (n : ℕ) :
    (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
  induction n with
  | zero =>
    have h1 : (∑ k in Finset.range 0, k ^ 3) = 0 := by
      clear * -
      aesop (config := {
      maxNormIterations       := 120
      maxGoals                := 64
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by exfalso))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by ring_nf at *))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by bound))
      (add unsafe 90% (by ext))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by linarith))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 90% (by simp))
      (add unsafe 80% (by gcongr))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 30% (by first | apply Ideal.Quotient.mk_eq_mk_iff_sub_mem | rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] | simp only [Ideal.Quotient.mk_eq_mk_iff_sub_mem]))
      (add unsafe 30% (by first | apply LieModuleHom.coe_linear_mk | rw [LieModuleHom.coe_linear_mk] | simp only [LieModuleHom.coe_linear_mk]))
      (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h2 : (∑ k in Finset.range 0, k) = 0 := by
      clear * -
      aesop (config := {
      maxNormIterations       := 120
      maxGoals                := 64
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by exfalso))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by ring_nf at *))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by bound))
      (add unsafe 90% (by ext))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by linarith))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 90% (by simp))
      (add unsafe 80% (by gcongr))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 30% (by first | apply DoubleCentralizer.zero_toProd | rw [DoubleCentralizer.zero_toProd] | simp only [DoubleCentralizer.zero_toProd]))
      (add unsafe 30% (by first | apply LieModuleHom.coe_linear_mk | rw [LieModuleHom.coe_linear_mk] | simp only [LieModuleHom.coe_linear_mk]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h3 : (∑ k in Finset.range 0, k) ^ 2 = 0 ^ 2 := by
      clear * - h2
      aesop (config := {
      maxNormIterations       := 120
      maxGoals                := 64
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h4 : 0 ^ 2 = 0 := by
      clear * -
      aesop (config := {
      maxNormIterations       := 160
      enableUnfold            := false
      })
      (add safe 2 (by ring))
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by ring_nf))
      (add unsafe 100% (by ring_nf at *))
      (add unsafe 100% (by split))
      (add unsafe 90% (by bound))
      (add unsafe 90% (by ext))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by linarith))
      (add unsafe 90% (by simp))
      (add unsafe 70% (by nlinarith))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 40% (by first | apply Real.sq_sqrt | rw [Real.sq_sqrt] | simp only [Real.sq_sqrt]))
      (add unsafe 30% (by first | apply sq_eq_zero_iff | rw [sq_eq_zero_iff] | simp only [sq_eq_zero_iff]))
      (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
      (add unsafe 10% (by first | apply MulZeroClass | rw [MulZeroClass] | simp only [MulZeroClass]))
      (add unsafe 10% (by first | apply sq_sub_sq | rw [sq_sub_sq] | simp only [sq_sub_sq]))
      (add unsafe 10% (by first | apply two_ne_zero | rw [two_ne_zero] | simp only [two_ne_zero]))
      (add unsafe 10% (by first | apply zero_pow | rw [zero_pow] | simp only [zero_pow]))

    have h5 : (∑ k in Finset.range 0, k ^ 3) = (∑ k in Finset.range 0, k) ^ 2 := by
      clear * - h1 h3 h4
      aesop (config := {
      maxNormIterations       := 120
      maxGoals                := 64
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    exact h5

  | succ n ih =>
    have h7 : (∑ k in Finset.range (n + 1), k ^ 3) = (∑ k in Finset.range n, k ^ 3) + n ^ 3 := by
      clear * -
      apply Finset.sum_range_succ

    have h8 : (∑ k in Finset.range (n + 1), k ^ 3) = (∑ k in Finset.range n, k) ^ 2 + n ^ 3 := by
      clear * - h7 ih
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h9 : (∑ k in Finset.range (n + 1), k) = (∑ k in Finset.range n, k) + n := by
      clear * -
      rw [Finset.sum_range_succ, eq_comm]

    have h10 : ((∑ k in Finset.range n, k) + n) ^ 2 = (∑ k in Finset.range n, k) ^ 2 + 2 * n * (∑ k in Finset.range n, k) + n ^ 2 := by
      clear * -
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply DoubleCentralizer.zero_toProd | rw [DoubleCentralizer.zero_toProd] | simp only [DoubleCentralizer.zero_toProd]))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h11 : (∑ k in Finset.range n, k) = n * (n - (1 : ℕ)) / (2 : ℕ) := by
      clear * -
      induction n <;> simp [Finset.range_succ, *] at *
      induction ‹ℕ›
      ·
        simp_all only [Finset.range_zero, Finset.sum_empty, _root_.zero_le, Nat.sub_eq_zero_of_le, mul_zero, Nat.zero_div,
          add_zero, zero_add]
      · simp_all only [add_tsub_cancel_right]
        open Nat in ring_nf at * <;> omega

    have h12 : 2 * n * (∑ k in Finset.range n, k) = 2 * n * (n * (n - (1 : ℕ)) / (2 : ℕ)) := by
      clear * - h11
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h13 : 2 * n * (n * (n - (1 : ℕ)) / (2 : ℕ)) = n * (n * (n - (1 : ℕ))) := by
      clear * -
      cases n <;> simp [mul_assoc, mul_comm, mul_left_comm]
      rw [Nat.mul_div_cancel']
      · linarith only
      · obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd ‹_› <;> ring_nf <;> omega

    have h14 : n * (n * (n - (1 : ℕ))) = n ^ 3 - (n ^ 2 : ℕ) := by
      clear * -
      cases' n with n n
      ·
        simp_all only [_root_.zero_le, Nat.sub_eq_zero_of_le, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, tsub_self]
      · simp_all only [add_tsub_cancel_right]
        induction' n with n ih
        · simp_all only [zero_add, mul_zero, one_pow, tsub_self]
        · ring_nf
          omega

    have h15 : 2 * n * (∑ k in Finset.range n, k) = n ^ 3 - (n ^ 2 : ℕ) := by
      clear * - h11 h12 h13 h14
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h16 : ((∑ k in Finset.range n, k) + n) ^ 2 = (∑ k in Finset.range n, k) ^ 2 + (n ^ 3 - (n ^ 2 : ℕ)) + n ^ 2 := by
      clear * - h10 h15
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h17 : (n ^ 3 - (n ^ 2 : ℕ)) + n ^ 2 = n ^ 3 := by
      clear * -
      simp [pow_succ, sub_add_cancel]
      induction n <;> simp_all

    have h18 : ((∑ k in Finset.range n, k) + n) ^ 2 = (∑ k in Finset.range n, k) ^ 2 + n ^ 3 := by
      clear * - h16 h17
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h19 : (∑ k in Finset.range (n + 1), k) ^ 2 = (∑ k in Finset.range n, k) ^ 2 + n ^ 3 := by
      clear * - h9 h18
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    have h20 : (∑ k in Finset.range (n + 1), k ^ 3) = (∑ k in Finset.range (n + 1), k) ^ 2 := by
      clear * - h8 h19
      aesop (config := {
      maxNormIterations       := 120
      })
      (add safe 4 (by field_simp))
      (add safe 4 (by push_neg))
      (add unsafe 100% (by nlinarith))
      (add unsafe 100% (by simp_all))
      (add unsafe 90% (by field_simp [*] at *))
      (add unsafe 90% (by norm_num [*] at *))
      (add unsafe 80% (by gcongr))
      (add unsafe 80% (by linarith))
      (add unsafe 70% (by bound))
      (add unsafe 70% (by norm_cast at *))
      (add unsafe 70% (by omega))
      (add unsafe 70% (by positivity))
      (add unsafe 70% (by ring_nf at *))
      (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
      (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

    exact h20
