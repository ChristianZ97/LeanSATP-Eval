import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_459 (a b c d : ℚ) (h₀ : 3 * a = b + c + d) (h₁ : 4 * b = a + c + d)
    (h₂ : 2 * c = a + b + d) (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 := by
  let S : ℚ := a + b + c + d

  have h_step2 : 3 * a = S - a := by
    clear * - h₀
    (linarith)

  have h_step3 : 4 * a = S := by
    clear * - h_step2
    (linarith)

  have h_step4 : a = S / (4 : ℚ) := by
    clear * - h_step3
    simp_all only [S]
    (linarith)

  have h_step5 : 4 * b = S - b := by
    clear * - h₁
    (linarith)

  have h_step6 : 5 * b = S := by
    clear * - h_step5
    simp_all only [S]
    (linarith)

  have h_step7 : b = S / (5 : ℚ) := by
    clear * - h_step6
    simp_all only [S]
    (linarith)

  have h_step8 : 2 * c = S - c := by
    clear * - h₂
    (linarith)

  have h_step9 : 3 * c = S := by
    clear * - h_step8
    simp_all only [S]
    (linarith)

  have h_step10 : c = S / (3 : ℚ) := by
    clear * - h_step9
    simp_all only [S]
    (linarith)

  have h_step11 : 8 * (S / (4 : ℚ)) + 10 * (S / (5 : ℚ)) + 6 * (S / (3 : ℚ)) = 24 := by
    clear * - h₃ h_step4 h_step7 h_step10
    linarith [S]

  have h_step12 : 2 * S + 2 * S + 2 * S = 24 := by
    clear * - h_step11
    simp_all only [S]
    (linarith)

  have h_step13 : 6 * S = 24 := by
    clear * - h_step12
    simp_all only [S]
    (linarith)

  have h_step14 : S = (4 : ℚ) := by
    clear * - h_step13
    simp_all only [S]
    (linarith)

  have h_step15 : a = (4 : ℚ) / 4 := by
    clear * - h_step4 h_step14
    linarith

  have h_step16 : a = (1 : ℚ) := by
    clear * - h_step15
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

  have h_step17 : b = (4 : ℚ) / 5 := by
    clear * - h_step7 h_step14
    simpa [h_step7, h_step14] using Eq.symm <| by ring

  have h_step18 : c = (4 : ℚ) / 3 := by
    clear * - h_step10 h_step14
    linarith [h_step10, h_step14]

  have h_step19 : d = S - a - b - c := by
    clear * -
    (linarith)

  have h_step20 : d = (4 : ℚ) - (1 : ℚ) - ((4 : ℚ) / 5) - ((4 : ℚ) / 3) := by
    clear * - h_step19 h_step14 h_step16 h_step17 h_step18
    subst h_step16 h_step17 h_step18
    (linarith)

  have h_step21 : d = (3 : ℚ) - ((4 : ℚ) / 5) - ((4 : ℚ) / 3) := by
    clear * - h_step20
    simp_all only [sub_left_inj]
    (linarith)

  have h_step22 : d = (3 : ℚ) - ((12 : ℚ) / 15) - ((20 : ℚ) / 15) := by
    clear * - h_step21
    subst h_step21
    (linarith)

  have h_step23 : d = (3 : ℚ) - ((32 : ℚ) / 15) := by
    clear * - h_step22
    subst h_step22
    (linarith)

  have h_step24 : d = ((45 : ℚ) / 15) - ((32 : ℚ) / 15) := by
    clear * - h_step23
    simp_all only [sub_left_inj]
    (linarith)

  have h_step25 : d = ((13 : ℚ) / 15) := by
    clear * - h_step24
    simp_all only
    (linarith)

  have h_step26 : d.num = 13 := by
    clear * - h_step25
    simp_all only
    (bound )

  have h_step27 : d.den = 15 := by
    clear * - h_step25
    simp_all only
    (bound )

  have h_step28 : ↑d.den + d.num = 13 + 15 := by
    clear * - h_step26 h_step27
    simp_all only [Nat.cast_ofNat, Int.reduceAdd]

  have h_step29 : ↑d.den + d.num = 28 := by
    clear * - h_step28
    simp_all only [Int.reduceAdd]

  exact h_step29
