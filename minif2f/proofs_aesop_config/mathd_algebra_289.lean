import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_289 (k t m n : ℕ) (h₀ : Nat.Prime m ∧ Nat.Prime n) (h₁ : t < k)
    (h₂ : (k ^ 2 : ℤ) - m * k + n = 0) (h₃ : (t ^ 2 : ℤ) - m * t + n = 0) :
    m ^ n + n ^ m + k ^ t + t ^ k = 20 := by
  have h_step1 : m = k + t := by
    clear * - h₁ h₂ h₃
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

  have h_step2 : n = k * t := by
    clear * - h_step1 h₂
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

  have h_step3 : t = 1 := by
    clear * - h₀ h₁ h_step2
    simp_all only
    replace h₀ := h₀.2
    have ht : t ≠ 0
    · simp_all only [ne_eq]
      intro ht_zero
      simp_all only [mul_zero]
      exact Nat.not_prime_zero h₀
    · simp_all only [ne_eq]
      replace h₀ := Nat.prime_mul_iff.mp h₀ <;> aesop

  have h_step4 : k = n := by
    clear * - h_step3 h_step2
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

  have h_step5 : m = n + 1 := by
    clear * - h_step1 h_step3 h_step4
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

  have h_step6 : n = 2 := by
    clear * - h₀ h_step5
    simp_all only
    obtain ⟨h₁, h₂⟩ := h₀
    have := h₁.eq_two_or_odd <;> have := h₂.eq_two_or_odd <;> aesop
    have hh := h₁.eq_two_or_odd <;> have h := h₂.eq_two_or_odd <;> omega

  have h_step7 : m = 3 := by
    clear * - h_step5 h_step6
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
    (add unsafe 30% (by first | apply Matroid.Indep.ssubset_ground | rw [Matroid.Indep.ssubset_ground] | simp only [Matroid.Indep.ssubset_ground]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))

  have h_step8 : k = 2 := by
    clear * - h_step4 h_step6
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

  have h_step9 : m ^ n + n ^ m + k ^ t + t ^ k = 3 ^ 2 + 2 ^ 3 + 2 ^ 1 + 1 ^ 2 := by
    clear * - h_step3 h_step4 h_step6 h_step7 h_step8
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

  have h_step10 : 3 ^ 2 = 9 := by
    clear * -
    aesop
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 40% (by first | apply QuaternionGroup.xa_sq | rw [QuaternionGroup.xa_sq] | simp only [QuaternionGroup.xa_sq]))
    (add unsafe 40% (by first | apply Real.rpow_two | rw [Real.rpow_two] | simp only [Real.rpow_two]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
    (add unsafe 10% (by first | apply CoxeterSystem.simple_sq | rw [CoxeterSystem.simple_sq] | simp only [CoxeterSystem.simple_sq]))
    (add unsafe 10% (by first | apply mul_pow | rw [mul_pow] | simp only [mul_pow]))
    (add unsafe 10% (by first | apply sq_sub_sq | rw [sq_sub_sq] | simp only [sq_sub_sq]))

  have h_step11 : 2 ^ 3 = 8 := by
    clear * -
    aesop
    (add safe 2 (by ring))
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by exfalso))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Nat.cast_two | rw [Nat.cast_two] | simp only [Nat.cast_two]))
    (add unsafe 40% (by first | apply QuaternionGroup.xa_sq | rw [QuaternionGroup.xa_sq] | simp only [QuaternionGroup.xa_sq]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq_eq_one_of_squarefree | rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree] | simp only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
    (add unsafe 10% (by first | apply gaussSum_sq | rw [gaussSum_sq] | simp only [gaussSum_sq]))
    (add unsafe 10% (by first | apply quadraticChar_sq_one | rw [quadraticChar_sq_one] | simp only [quadraticChar_sq_one]))
    (add unsafe 10% (by first | apply quadraticChar_sq_one' | rw [quadraticChar_sq_one'] | simp only [quadraticChar_sq_one']))

  have h_step12 : 2 ^ 1 = 2 := by
    clear * -
    aesop
    (add safe 2 (by ring))
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by exfalso))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 40% (by first | apply Complex.cpow_two | rw [Complex.cpow_two] | simp only [Complex.cpow_two]))
    (add unsafe 40% (by first | apply Nat.factorial_two | rw [Nat.factorial_two] | simp only [Nat.factorial_two]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq_eq_one_of_squarefree | rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree] | simp only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
    (add unsafe 10% (by first | apply Nat.cast_two | rw [Nat.cast_two] | simp only [Nat.cast_two]))
    (add unsafe 10% (by first | apply Polynomial.derivative_sq | rw [Polynomial.derivative_sq] | simp only [Polynomial.derivative_sq]))
    (add unsafe 10% (by first | apply Surreal.nsmul_pow_two_powHalf | rw [Surreal.nsmul_pow_two_powHalf] | simp only [Surreal.nsmul_pow_two_powHalf]))

  have h_step13 : 1 ^ 2 = 1 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
  })
    (add safe 2 (by ring))
    (add safe 3 (by norm_cast))
    (add safe 4 (by abel))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by exfalso))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by omega))
    (add unsafe 80% (by split))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 30% (by first | apply legendreSym.sq_one | rw [legendreSym.sq_one] | simp only [legendreSym.sq_one]))
    (add unsafe 30% (by first | apply one_pow | rw [one_pow] | simp only [one_pow]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq_eq_one_of_squarefree | rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree] | simp only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
    (add unsafe 10% (by first | apply MulChar.IsQuadratic.sq_eq_one | rw [MulChar.IsQuadratic.sq_eq_one] | simp only [MulChar.IsQuadratic.sq_eq_one]))
    (add unsafe 10% (by first | apply quadraticChar_sq_one | rw [quadraticChar_sq_one] | simp only [quadraticChar_sq_one]))
    (add unsafe 10% (by first | apply quadraticChar_sq_one' | rw [quadraticChar_sq_one'] | simp only [quadraticChar_sq_one']))

  have h_step14 : m ^ n + n ^ m + k ^ t + t ^ k = 9 + 8 + 2 + 1 := by
    clear * - h_step9 h_step10 h_step11 h_step12 h_step13
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

  have h_step15 : 9 + 8 = 17 := by
    clear * -
    aesop (config := {
    maxGoals                := 64
  })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by nlinarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by interval_cases))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply TrivSqZeroExt.exp_inr | rw [TrivSqZeroExt.exp_inr] | simp only [TrivSqZeroExt.exp_inr]))
    (add unsafe 10% (by first | apply goldenRatio | rw [goldenRatio] | simp only [goldenRatio]))

  have h_step16 : 17 + 2 = 19 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
  })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Int.cast_two | rw [Int.cast_two] | simp only [Int.cast_two]))
    (add unsafe 40% (by first | apply ack_two | rw [ack_two] | simp only [ack_two]))
    (add unsafe 40% (by first | apply one_add_one_eq_two | rw [one_add_one_eq_two] | simp only [one_add_one_eq_two]))
    (add unsafe 30% (by first | apply Nat.fib_two_mul_add_two | rw [Nat.fib_two_mul_add_two] | simp only [Nat.fib_two_mul_add_two]))
    (add unsafe 10% (by first | apply Nat.fib_two_mul_add_one | rw [Nat.fib_two_mul_add_one] | simp only [Nat.fib_two_mul_add_one]))
    (add unsafe 10% (by first | apply two_mul | rw [two_mul] | simp only [two_mul]))

  have h_step17 : 19 + 1 = 20 := by
    clear * -
    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
    enableUnfold            := false
  })
    (add safe 2 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by positivity))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by interval_cases))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 30% (by first | apply PNat.eq | rw [PNat.eq] | simp only [PNat.eq]))
    (add unsafe 20% (by first | apply Nat.add_left_cancel | rw [Nat.add_left_cancel] | simp only [Nat.add_left_cancel]))
    (add unsafe 20% (by first | apply Ordinal.add_left_cancel | rw [Ordinal.add_left_cancel] | simp only [Ordinal.add_left_cancel]))
    (add unsafe 10% (by first | apply ArithmeticFunction.intCoe_apply | rw [ArithmeticFunction.intCoe_apply] | simp only [ArithmeticFunction.intCoe_apply]))
    (add unsafe 10% (by first | apply ArithmeticFunction.natCoe_apply | rw [ArithmeticFunction.natCoe_apply] | simp only [ArithmeticFunction.natCoe_apply]))
    (add unsafe 10% (by first | apply ONote.repr_ofNat | rw [ONote.repr_ofNat] | simp only [ONote.repr_ofNat]))

  have h_step18 : m ^ n + n ^ m + k ^ t + t ^ k = 20 := by
    clear * - h_step14 h_step15 h_step16 h_step17
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

  exact h_step18
