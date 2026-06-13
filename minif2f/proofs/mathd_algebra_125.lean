import Mathlib
open BigOperators Real Nat Topology Rat
/-- Today a father's age is five times his son's age. Exactly three years ago, the sum of their ages was 30. How old is the son today? Show that it is 6.-/

theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by

    subst h₁
    simp_all only [ofNat_pos, mul_pos_iff_of_pos_left, and_self, Nat.cast_mul, Nat.cast_ofNat]
    (nlinarith)