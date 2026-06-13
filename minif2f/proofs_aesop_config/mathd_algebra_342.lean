import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_342 (a d : ℝ) (h₀ : (∑ k in Finset.range 5, (a + k * d)) = 70)
    (h₁ : (∑ k in Finset.range 10, (a + k * d)) = 210) : a = 42 / 5 := by
  have h₂ : (5 : ℝ) * a + d * (∑ k in Finset.range 5, (k : ℝ)) = (70 : ℝ) := by
    clear * - h₀
    simp only [Finset.sum, Finset.range_succ] at h₀
    simp_all only [Finset.range_zero, insert_emptyc_eq, Finset.insert_val, Finset.singleton_val, Multiset.mem_singleton,
    one_ne_zero, not_false_eq_true, Multiset.ndinsert_of_not_mem, Multiset.mem_cons, OfNat.ofNat_ne_one,
    OfNat.ofNat_ne_zero, or_self, Nat.succ_ne_self, reduceEqDiff, Multiset.map_cons, Nat.cast_ofNat, Nat.cast_one,
    one_mul, Multiset.map_singleton, CharP.cast_eq_zero, zero_mul, add_zero, Multiset.sum_cons, Multiset.sum_singleton]
    simp [Finset.sum_range_succ, add_comm] <;> linarith

  have h₃ : (∑ k in Finset.range 5, (k : ℝ)) = (10 : ℝ) := by
    clear * -
    (ring_nf at *)

  have h₄ : (5 : ℝ) * a + (10 : ℝ) * d = (70 : ℝ) := by
    clear * - h₂ h₃
    simp_all only
    (nlinarith)

  have h₅ : (10 : ℝ) * a + d * (∑ k in Finset.range 10, (k : ℝ)) = (210 : ℝ) := by
    clear * - h₁
    simp [Finset.sum_range_succ, add_comm a] at * <;> linarith

  have h₆ : (∑ k in Finset.range 10, (k : ℝ)) = (45 : ℝ) := by
    clear * -
    (ring_nf at *)

  have h₇ : (10 : ℝ) * a + (45 : ℝ) * d = (210 : ℝ) := by
    clear * - h₅ h₆
    simp_all only
    (nlinarith)

  have h₈ : a + (2 : ℝ) * d = (14 : ℝ) := by
    clear * - h₄
    (nlinarith)

  have h₉ : a = (14 : ℝ) - (2 : ℝ) * d := by
    clear * - h₈
    (nlinarith)

  have h₁₀ : (10 : ℝ) * ((14 : ℝ) - (2 : ℝ) * d) + (45 : ℝ) * d = (210 : ℝ) := by
    clear * - h₇ h₉
    subst h₉
    simp_all only

  have h₁₁ : (140 : ℝ) - (20 : ℝ) * d + (45 : ℝ) * d = (210 : ℝ) := by
    clear * - h₁₀
    (nlinarith)

  have h₁₂ : (140 : ℝ) + (25 : ℝ) * d = (210 : ℝ) := by
    clear * - h₁₁
    (nlinarith)

  have h₁₃ : (25 : ℝ) * d = (70 : ℝ) := by
    clear * - h₁₂
    (nlinarith)

  have h₁₄ : d = (70 : ℝ) / (25 : ℝ) := by
    clear * - h₁₃
    (field_simp)
    (nlinarith)

  have h₁₅ : d = (14 : ℝ) / (5 : ℝ) := by
    clear * - h₁₄
    subst h₁₄
    (field_simp)
    (nlinarith)

  have h₁₆ : a = (14 : ℝ) - (2 : ℝ) * ((14 : ℝ) / (5 : ℝ)) := by
    clear * - h₉ h₁₅
    subst h₉ h₁₅
    simp_all only

  have h₁₇ : a = (14 : ℝ) - ((28 : ℝ) / (5 : ℝ)) := by
    clear * - h₁₆
    subst h₁₆
    simp_all only [sub_right_inj]
    (field_simp)
    (nlinarith)

  have h₁₈ : a = ((70 : ℝ) / (5 : ℝ)) - ((28 : ℝ) / (5 : ℝ)) := by
    clear * - h₁₇
    subst h₁₇
    simp_all only [sub_left_inj]
    (field_simp)
    (nlinarith)

  have h₁₉ : a = (42 : ℝ) / (5 : ℝ) := by
    clear * - h₁₈
    subst h₁₈
    (field_simp)
    (nlinarith)

  exact h₁₉