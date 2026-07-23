import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_342 (a d : ℝ) (h₀ : (∑ k in Finset.range 5, (a + k * d)) = 70)
    (h₁ : (∑ k in Finset.range 10, (a + k * d)) = 210) : a = 42 / 5 := by
  have h₂ : (5 : ℝ) * a + d * (∑ k in Finset.range 5, (k : ℝ)) = (70 : ℝ) := by
    clear * - h₀
    simp [add_comm, Finset.sum] at *
    linear_combination h₀

  have h₃ : (∑ k in Finset.range 5, (k : ℝ)) = (10 : ℝ) := by
    clear * -
    (ring)

  have h₄ : (5 : ℝ) * a + (10 : ℝ) * d = (70 : ℝ) := by
    clear * - h₂ h₃
    simp_all only
    (linarith)

  have h₅ : (10 : ℝ) * a + d * (∑ k in Finset.range 10, (k : ℝ)) = (210 : ℝ) := by
    clear * - h₁
    try simp only [Finset.sum_range_succ] at h₁
    simp at * <;> norm_num at h₁ ⊢ <;> linarith

  have h₆ : (∑ k in Finset.range 10, (k : ℝ)) = (45 : ℝ) := by
    clear * -
    (bound )

  have h₇ : (10 : ℝ) * a + (45 : ℝ) * d = (210 : ℝ) := by
    clear * - h₅ h₆
    simp_all only
    (linarith)

  have h₈ : a + (2 : ℝ) * d = (14 : ℝ) := by
    clear * - h₄
    (linarith)

  have h₉ : a = (14 : ℝ) - (2 : ℝ) * d := by
    clear * - h₈
    (linarith)

  have h₁₀ : (10 : ℝ) * ((14 : ℝ) - (2 : ℝ) * d) + (45 : ℝ) * d = (210 : ℝ) := by
    clear * - h₇ h₉
    (linarith)

  have h₁₁ : (140 : ℝ) - (20 : ℝ) * d + (45 : ℝ) * d = (210 : ℝ) := by
    clear * - h₁₀
    (linarith)

  have h₁₂ : (140 : ℝ) + (25 : ℝ) * d = (210 : ℝ) := by
    clear * - h₁₁
    (linarith)

  have h₁₃ : (25 : ℝ) * d = (70 : ℝ) := by
    clear * - h₁₂
    (linarith)

  have h₁₄ : d = (70 : ℝ) / (25 : ℝ) := by
    clear * - h₁₃
    (linarith)

  have h₁₅ : d = (14 : ℝ) / (5 : ℝ) := by
    clear * - h₁₄
    simp_all only
    (linarith)

  have h₁₆ : a = (14 : ℝ) - (2 : ℝ) * ((14 : ℝ) / (5 : ℝ)) := by
    clear * - h₉ h₁₅
    simp_all only

  have h₁₇ : a = (14 : ℝ) - ((28 : ℝ) / (5 : ℝ)) := by
    clear * - h₁₆
    simp_all only [sub_right_inj]
    (linarith)

  have h₁₈ : a = ((70 : ℝ) / (5 : ℝ)) - ((28 : ℝ) / (5 : ℝ)) := by
    clear * - h₁₇
    subst h₁₇
    simp_all only [sub_left_inj]
    (linarith)

  have h₁₉ : a = (42 : ℝ) / (5 : ℝ) := by
    clear * - h₁₈
    subst h₁₈
    (linarith)

  exact h₁₉
