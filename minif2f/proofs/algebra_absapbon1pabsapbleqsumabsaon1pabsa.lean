import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have h1 : abs (a + b) ≤ abs a + abs b := by
    clear * -
    cases' abs_cases (a + b) with ab_nonneg ab_nonpos <;> cases' abs_cases a <;> cases' abs_cases b <;> linarith

  have h2 : 0 ≤ abs a + abs b - abs (a + b) := by
    clear * - h1
    linarith

  have h_pos_1 : 0 < (1:ℝ) + abs (a + b) := by
    clear * -
    positivity

  have h_pos_2 : 0 < (1:ℝ) + abs a + abs b := by
    clear * -
    positivity

  have h_pos_prod : 0 < ((1:ℝ) + abs (a + b)) * ((1:ℝ) + abs a + abs b) := by
    clear * - h_pos_1 h_pos_2
    (nlinarith)

  have h3 : 0 ≤ (abs a + abs b - abs (a + b)) / (((1:ℝ) + abs (a + b)) * ((1:ℝ) + abs a + abs b)) := by
    clear * - h2 h_pos_prod
    (bound )

  have h4 : (abs a + abs b - abs (a + b)) / (((1:ℝ) + abs (a + b)) * ((1:ℝ) + abs a + abs b)) =
           (abs a + abs b) / ((1:ℝ) + abs a + abs b) - abs (a + b) / ((1:ℝ) + abs (a + b)) := by
    clear * -
    (field_simp [mabs_of_one_lt] at *)
    (grind only [div_div])

  have h5 : 0 ≤ (abs a + abs b) / ((1:ℝ) + abs a + abs b) - abs (a + b) / ((1:ℝ) + abs (a + b)) := by
    clear * - h3 h4
    simp_all only [sub_nonneg]

  have h5_rearr : abs (a + b) / ((1:ℝ) + abs (a + b)) ≤ (abs a + abs b) / ((1:ℝ) + abs a + abs b) := by
    clear * - h5
    simp_all only [sub_nonneg]

  have h6 : abs a / ((1:ℝ) + abs a) + abs b / ((1:ℝ) + abs b) =
          (abs a * ((1:ℝ) + abs b) + abs b * ((1:ℝ) + abs a)) / (((1:ℝ) + abs a) * ((1:ℝ) + abs b)) := by
    clear * -
    (field_simp [abs_mul] at *)

  have h7 : abs a / ((1:ℝ) + abs a) + abs b / ((1:ℝ) + abs b) =
          ((abs a + abs b) + 2 * abs a * abs b) / ((1:ℝ) + (abs a + abs b) + abs a * abs b) := by
    clear * - h6
    simp_all only
    (field_simp [mabs_of_one_lt] at *)
    simp_all only
    (grind only [Real.norm_eq_abs])

  let LHS := abs a / ((1:ℝ) + abs a) + abs b / ((1:ℝ) + abs b)
  let MID := (abs a + abs b) / ((1:ℝ) + abs a + abs b)

  have h8 : LHS - MID =
        (((abs a + abs b) + 2 * abs a * abs b) * ((1:ℝ) + abs a + abs b) - (abs a + abs b) * ((1:ℝ) + (abs a + abs b) + abs a * abs b)) /
         (((1:ℝ) + abs a) * ((1:ℝ) + abs b) * ((1:ℝ) + abs a + abs b)) := by
    clear * - h7
    simp_all only [LHS, MID]
    (ring_nf)
    simp_all only [sq_abs]
    (ring_nf)
    (field_simp [mabs_of_one_lt] at *)
    simp_all only [add_sub_add_right_eq_sub, sub_add_cancel_left, mul_neg]
    (ring_nf)
    simp_all only [sq_abs]
    (ring_nf)

  have h9 : LHS - MID =
          (abs a * abs b * ((2:ℝ) + abs a + abs b)) / (((1:ℝ) + abs a) * ((1:ℝ) + abs b) * ((1:ℝ) + abs a + abs b)) := by
    clear * - h8
    simp_all only [LHS, MID]
    (field_simp [mabs_of_one_lt] at *)
    (ring_nf)

  have h10 : abs a * abs b * ((2:ℝ) + abs a + abs b) ≥ 0 := by
    clear * -
    (bound )

  have h11 : 0 < ((1:ℝ) + abs a) * ((1:ℝ) + abs b) * ((1:ℝ) + abs a + abs b) := by
    clear * -
    positivity

  have h12 : LHS - MID ≥ 0 := by
    clear * - h9 h10 h11
    simp_all only [LHS, MID]
    (bound )

  have h13 : MID ≤ LHS := by
    clear * - h12
    simp_all only [ge_iff_le, sub_nonneg, LHS, MID]

  have h14 : abs (a + b) / ((1:ℝ) + abs (a + b)) ≤ abs a / ((1:ℝ) + abs a) + abs b / ((1:ℝ) + abs b) := by
    clear * - h5_rearr h13
    simp_all only [MID, LHS]
    (linarith)

  exact h14
