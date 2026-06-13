import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  have h1 : (10 : ℤ) = (11 : ℤ) + (-1 : ℤ) := by
    clear * -
    aesop (config := {
    maxGoals                := 64
    })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by linarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply EReal.coe_neg | rw [EReal.coe_neg] | simp only [EReal.coe_neg]))
    (add unsafe 30% (by first | apply EReal.neg_bot | rw [EReal.neg_bot] | simp only [EReal.neg_bot]))
    (add unsafe 30% (by first | apply EReal.neg_top | rw [EReal.neg_top] | simp only [EReal.neg_top]))
    (add unsafe 30% (by first | apply inv_neg_one | rw [inv_neg_one] | simp only [inv_neg_one]))
    (add unsafe 10% (by first | apply EReal.inv_bot | rw [EReal.inv_bot] | simp only [EReal.inv_bot]))
    (add unsafe 10% (by first | apply EReal.inv_top | rw [EReal.inv_top] | simp only [EReal.inv_top]))
    (add unsafe 10% (by first | apply Pell.Solution₁.y_inv | rw [Pell.Solution₁.y_inv] | simp only [Pell.Solution₁.y_inv]))

  have h2 : (10 : ℤ) ^ n = ((11 : ℤ) + (-1 : ℤ)) ^ n := by
    clear * - h1
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

  have h3 : ((11 : ℤ) + (-1 : ℤ)) ^ n = ∑ k in Finset.range (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) := by
    clear * -
    simp_all only [Int.reduceNeg, Int.reduceAdd]
    have A := (add_pow 11 (-1) n).symm
    simp_all only [Int.reduceNeg, Int.reduceAdd]
    nth_rewrite 1 [← A]
    simp_all only [Int.reduceNeg]
    simp [← A, mul_comm, mul_assoc, mul_left_comm, ← mul_add]

  have h4 : ((11 : ℤ) + (-1 : ℤ)) ^ n = (Nat.choose n 0 : ℤ) * (11 : ℤ) ^ 0 * (-1 : ℤ) ^ n + ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) := by
    clear * - h3
    simp_all only [Int.reduceNeg, Int.reduceAdd, choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul]
    simp [Finset.sum_Ico_eq_sub, ← h3]

  have h5 : (Nat.choose n 0 : ℤ) * (11 : ℤ) ^ 0 * (-1 : ℤ) ^ n = (-1 : ℤ) ^ n := by
    clear * -
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

  have h6 : (10 : ℤ) ^ n = (-1 : ℤ) ^ n + ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) := by
    clear * - h2 h4 h5
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
    (add unsafe 30% (by first | apply Subspace.quotAnnihilatorEquiv_apply | rw [Subspace.quotAnnihilatorEquiv_apply] | simp only [Subspace.quotAnnihilatorEquiv_apply]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h7 : (10 : ℤ) ^ n - (-1 : ℤ) ^ n = ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) := by
    clear * - h6
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

  have h8 : ∀ k ∈ Finset.Ico 1 (n + 1), (11 : ℤ) ^ k = (11 : ℤ) * (11 : ℤ) ^ (k - 1) := by
    clear * -
    simp_all
    intro k _ hk2
    cases k <;> simp [pow_succ]
    · simp_all
    · simp_all
      rw [mul_comm]

  have h9 : ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) = ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) * (11 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (n - k) := by
    clear * - h8
    simp_all
    refine' Finset.sum_congr rfl _
    simp_all
    simp [mul_assoc, mul_left_comm] <;> intros <;> aesop

  have h10 : ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) * (11 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (n - k) = (11 : ℤ) * ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (n - k) := by
    clear * - h9
    clear h9
    simp [Finset.mul_sum, mul_assoc, Nat.cast_comm]

  have h11 : (10 : ℤ) ^ n - (-1 : ℤ) ^ n = (11 : ℤ) * ∑ k in Finset.Ico 1 (n + 1), (Nat.choose n k : ℤ) * (11 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (n - k) := by
    clear * - h7 h9 h10
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

  have h12 : ∃ (m : ℤ), (10 : ℤ) ^ n - (-1 : ℤ) ^ n = (11 : ℤ) * m := by
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

  have h13 : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
    clear * - h12
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

  exact h13
