/-
mathd_algebra_362 (MiniF2F-test).  Each `have` is one sketch gap; the tag marks
which solver closed it.  [satp] = 0.2B SATP policy, [bfs] = BFS-Prover-V2-7B.
Verifies with `import Mathlib` alone.
-/
import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_362 (a b : ℝ) (h₀ : a ^ 2 * b ^ 3 = 32 / 27) (h₁ : a / b ^ 3 = 27 / 4) :
    a + b = 8 / 3 := by
  -- [satp]  multiply the two hypotheses
  have h2 : a ^ 2 * b ^ 3 * (a / b ^ 3) = (32 / 27) * (27 / 4) := by
    clear * - h₀ h₁
    simp_all only
  -- [bfs]  reduce to a³ = 8 (case-split on b)
  have h3 : a ^ 3 = 8 := by
    clear * - h2
    rcases eq_or_ne b 0 with (rfl | hb)
    ·
      simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero, zero_eq_mul,
        div_eq_zero_iff, or_self]
    · simp_all only [ne_eq]
      field_simp at * <;> ring
      apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 3 hb)) <;> nlinarith
  -- [bfs]  cube root: a = 2
  have h4 : a = (2 : ℝ) := by
    clear * - h3
    nlinarith [sq_nonneg (a ^ 2)]
  -- [satp]  substitute a = 2
  have h5 : (2 : ℝ) / b ^ 3 = 27 / 4 := by
    clear * - h4 h₁
    subst h4
    simp_all only
  -- [bfs]  solve b³ = 8/27
  have h6 : b ^ 3 = 8 / 27 := by
    clear * - h5
    rcases eq_or_ne b 0 with (rfl | hb) <;> field_simp at * <;> linarith
  -- [bfs]  cube root: b = 2/3
  have h7 : b = (2 : ℝ) / 3 := by
    clear * - h6
    nlinarith [sq_nonneg (b ^ 2 - 4 / 9)]
  -- [satp]  assemble a + b
  have h8 : a + b = (2 : ℝ) + (2 : ℝ) / 3 := by
    clear * - h4 h7
    subst h7 h4
    simp_all only
  -- [satp]  normalise to 8/3
  have h9 : a + b = 8 / 3 := by
    clear * - h8
    simp_all only
    (field_simp)
    (nlinarith)
  exact h9
