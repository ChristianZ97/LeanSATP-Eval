import Mathlib
open BigOperators Real Nat Topology Rat
/-- Because of redistricting, Liberty Middle School's enrollment increased to 598 students. This is an increase of $4\%$ over last year's enrollment. What was last year's enrollment? Show that it is 575\text{ students}.-/

theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 := by

    (field_simp [*] at *)
    (norm_cast at *)
    simp_all only [reduceMul]
    (nlinarith)