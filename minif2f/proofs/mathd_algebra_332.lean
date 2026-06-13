import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have h_s2 : x + y = (14:ℝ) := by
    clear * - h₀
    (nlinarith)

  have h_s4 : x * y = (19:ℝ) := by
    clear * - h₁
    erw [Real.sqrt_eq_iff_sq_eq] at h₁
    · simp_all only [ofNat_nonneg, sq_sqrt]
    · exact le_of_lt (sqrt_pos.1 (by aesop))
    · simp_all only [Real.sqrt_nonneg]

  have h_s5 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    clear * -
    (nlinarith)

  have h_s6 : x ^ 2 + y ^ 2 = ((14:ℝ) ^ 2) - 2 * ((19:ℝ)) := by
    clear * - h_s2 h_s4 h_s5
    simp_all only

  have h_l1 : ((14:ℝ) ^ 2) = (196:ℝ) := by
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
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply QuaternionGroup.xa_sq | rw [QuaternionGroup.xa_sq] | simp only [QuaternionGroup.xa_sq]))
    (add unsafe 40% (by first | apply Real.sq_sqrt | rw [Real.sq_sqrt] | simp only [Real.sq_sqrt]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq | rw [ArithmeticFunction.moebius_sq] | simp only [ArithmeticFunction.moebius_sq]))
    (add unsafe 10% (by first | apply ArithmeticFunction.moebius_sq_eq_one_of_squarefree | rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree] | simp only [ArithmeticFunction.moebius_sq_eq_one_of_squarefree]))
    (add unsafe 10% (by first | apply CoxeterSystem.simple_sq | rw [CoxeterSystem.simple_sq] | simp only [CoxeterSystem.simple_sq]))
    (add unsafe 10% (by first | apply MulChar.IsQuadratic.sq_eq_one | rw [MulChar.IsQuadratic.sq_eq_one] | simp only [MulChar.IsQuadratic.sq_eq_one]))
    (add unsafe 10% (by first | apply quadraticChar_sq_one' | rw [quadraticChar_sq_one'] | simp only [quadraticChar_sq_one']))
    (add unsafe 10% (by first | apply sq_add_sq_mul | rw [sq_add_sq_mul] | simp only [sq_add_sq_mul]))

  have h_s7 : x ^ 2 + y ^ 2 = (196:ℝ) - 2 * ((19:ℝ)) := by
    clear * - h_s6 h_l1
    simp_all only

  have h_l2 : 2 * ((19:ℝ)) = (38:ℝ) := by
    clear * -
    (ring)

  have h_s8 : x ^ 2 + y ^ 2 = (196:ℝ) - (38:ℝ) := by
    clear * - h_s7 h_l2
    simp_all only

  have h_l3 : (196:ℝ) - (38:ℝ) = (158:ℝ) := by
    clear * -
    (ring)

  have h_s9 : x ^ 2 + y ^ 2 = (158:ℝ) := by
    clear * - h_s8 h_l3
    simp_all only

  exact h_s9
