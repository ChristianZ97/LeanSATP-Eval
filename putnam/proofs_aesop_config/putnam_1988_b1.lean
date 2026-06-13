
import Mathlib
open Set Filter Topology

set_option maxHeartbeats 0

theorem putnam_1988_b1
: ∀ a ≥ 2, ∀ b ≥ 2, ∃ x y z : ℤ, x > 0 ∧ y > 0 ∧ z > 0 ∧ a * b = x * y + x * z + y * z + 1 := by
  intro a ha b hb
  let z : ℤ := 1
  let x : ℤ := (a : ℤ) - 1
  let y : ℤ := (b : ℤ) - 1
  have hx_pos : x > 0 := by
    clear * - ha
    simp_all only [ge_iff_le, gt_iff_lt, sub_pos, x]
    exact ha

  have hy_pos : y > 0 := by
    clear * - hb
    simp_all only [ge_iff_le, gt_iff_lt, sub_pos, y]
    exact hb

  have hz_pos : z > 0 := by
    clear * -
    simp_all only [gt_iff_lt, zero_lt_one, z]

  have h_x_plus_1 : x + 1 = (a : ℤ) := by
    clear * -
    simp_all only [sub_add_cancel, x]

  have h_y_plus_1 : y + 1 = (b : ℤ) := by
    clear * -
    simp_all only [sub_add_cancel, y]

  have h_factor : (x + 1) * (y + 1) = x * y + x + y + 1 := by
    clear * -
    simp_all only [sub_add_cancel, x, y]
    (nlinarith)

  have h_subst_z : x * y + x * z + y * z + 1 = x * y + x + y + 1 := by
    clear * -
    simp_all only [mul_one, x, y, z]

  have h_prod : (x + 1) * (y + 1) = (a : ℤ) * (b : ℤ) := by
    clear * - h_x_plus_1 h_y_plus_1
    simp_all only [sub_add_cancel, x, y]

  have h_main : (a : ℤ) * (b : ℤ) = x * y + x * z + y * z + 1 := by
    clear * - h_prod h_factor h_subst_z
    simp_all only [sub_add_cancel, mul_one, x, y, z]

  use x, y, z