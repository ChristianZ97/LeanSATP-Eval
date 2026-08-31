import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_184 (a b : NNReal) (h₀ : 0 < a ∧ 0 < b) (h₁ : a ^ 2 = 6 * b)
    (h₂ : a ^ 2 = 54 / b) : a = 3 * NNReal.sqrt 2 := by
  have h_step1 : (6 : NNReal) * b = (54 : NNReal) / b := by
    clear * - h₁ h₂
    simp_all only

  have h_step2 : (6 : NNReal) * b ^ 2 = (54 : NNReal) := by
    clear * - h_step1 h₀
    field_simp at *
    all_goals aesop
    field_simp [mul_comm, pow_two] at * <;> norm_cast

  have h_step3 : b ^ 2 = (9 : NNReal) := by
    clear * - h_step2
    rw [← NNReal.coe_inj] at *
    simp [mul_comm] at h_step2
    simp [← NNReal.coe_inj] at *
    nlinarith [pow_two (b : ℝ)]

  have h_step4 : b = (3 : NNReal) := by
    clear * - h_step3 h₀
    cases' b with b
    simp [← NNReal.coe_inj] at *
    any_goals nlinarith [sq_nonneg b]

  have h_step5 : a ^ 2 = (6 : NNReal) * (3 : NNReal) := by
    clear * - h₁ h_step4
    simp_all only

  have h_step6 : a ^ 2 = (18 : NNReal) := by
    clear * - h_step5
    simp_all only
    (bound )

  have h_step7 : a = NNReal.sqrt (18 : NNReal) := by
    clear * - h_step6 h₀
    have ha : 0 < a := h₀.1
    have h : a ^ 2 = (18 : NNReal) := h_step6
    simp [← h]

  have h_step8 : a = NNReal.sqrt ((9 : NNReal) * (2 : NNReal)) := by
    clear * - h_step7
    subst h_step7
    simp only [EmbeddingLike.apply_eq_iff_eq] at *
    (ring)

  have h_step9 : a = NNReal.sqrt (9 : NNReal) * NNReal.sqrt (2 : NNReal) := by
    clear * - h_step8
    simp [h_step8, ← NNReal.sqrt_mul]

  have h_step10 : a = (3 : NNReal) * NNReal.sqrt (2 : NNReal) := by
    clear * - h_step9
    (bound )

  exact h_step10
