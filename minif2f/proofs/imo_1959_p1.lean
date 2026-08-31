import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h_step1 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd ((21 * n + 4 : ℕ) - (14 * n + 3 : ℕ)) (14 * n + 3) := by
    clear * -
    rewrite [Nat.gcd_sub_self_left]
    · simp only [add_tsub_cancel_left]
    · linarith

  have h_step2 : ((21 * n + 4 : ℕ) - (14 * n + 3 : ℕ)) = 7 * n + 1 := by
    clear * -
    simp_all only [reduceSubDiff]
    (omega)

  have h_step3 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (7 * n + 1) (14 * n + 3) := by
    clear * - h_step1 h_step2
    simp_all only [reduceSubDiff]

  have h_step4 : Nat.gcd (7 * n + 1) (14 * n + 3) = Nat.gcd (7 * n + 1) ((14 * n + 3 : ℕ) - (2 * (7 * n + 1) : ℕ)) := by
    clear * -
    simp [add_comm, add_left_comm]
    have : 3 + 14 * n = 2 * (1 + 7 * n) + 1 := by ring
    simp [this]

  have h_step5 : ((14 * n + 3 : ℕ) - (2 * (7 * n + 1) : ℕ)) = ((14 * n + 3 : ℕ) - (14 * n : ℕ)) - 2 := by
    clear * -
    simp_all only [add_tsub_cancel_left, reduceSub]
    (omega)

  have h_step6 : (((14 * n + 3 : ℕ) - (14 * n : ℕ)) - 2) = 1 := by
    clear * -
    simp_all only [add_tsub_cancel_left, reduceSub]

  have h_step7 : Nat.gcd (7 * n + 1) (14 * n + 3) = Nat.gcd (7 * n + 1) 1 := by
    clear * - h_step4 h_step5 h_step6
    simp_all only [add_tsub_cancel_left, reduceSub, Nat.gcd_one_right]

  have h_step8 : Nat.gcd (7 * n + 1) 1 = 1 := by
    clear * -
    simp_all only [Nat.gcd_one_right]

  have h_final : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    clear * - h_step3 h_step7 h_step8
    simp_all only [Nat.gcd_one_right]

  exact h_final
