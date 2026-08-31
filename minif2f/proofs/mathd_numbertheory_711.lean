import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_numbertheory_711 (m n : ℕ) (h₀ : 0 < m ∧ 0 < n) (h₁ : Nat.gcd m n = 8)
    (h₂ : Nat.lcm m n = 112) : 72 ≤ m + n := by
  have h_step1 : m * n = Nat.gcd m n * Nat.lcm m n := by
    clear * -
    simp_all only [Nat.gcd_mul_lcm]

  have h_step2 : m * n = 8 * 112 := by
    clear * - h_step1 h₁ h₂
    simp_all only [reduceMul]

  have h_step3 : m * n = 896 := by
    clear * - h_step2
    simp_all only [reduceMul]

  have h_div_m : 8 ∣ m := by
    clear * - h₁
    have : m.gcd n = 8 := h₁
    have hdvd := Nat.gcd_dvd_left m n
    rewrite [this] at hdvd <;> tauto

  have h_div_n : 8 ∣ n := by
    clear * - h₁
    have : m.gcd n = 8 := h₁
    have : m.gcd n = 8 := this
    have := Nat.gcd_dvd_right m n <;> aesop

  let a := (m : ℕ) / 8
  let b := (n : ℕ) / 8

  have h_step4 : m = 8 * a := by
    clear * - h_div_m
    simp_all only [a]
    (omega)

  have h_step5 : n = 8 * b := by
    clear * - h_div_n
    simp_all only [b]
    (omega)

  have h_step6 : 8 * a * (8 * b) = 896 := by
    clear * - h_step3 h_step4 h_step5
    simp_all [-mul_assoc]

  have h_step7 : 64 * a * b = 896 := by
    clear * - h_step6
    simp_all only [a, b]
    (linarith)

  have h_step8 : a * b = 14 := by
    clear * - h_step7
    simp_all only [a, b]
    (linarith)

  have h_step_cases : a + b = 15 ∨ a + b = 9 := by
    clear * - h_step8 h₀
    by_contra hh
    rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> aesop
    any_goals
    have : a < 14 := by nlinarith
    have : b < 14 := by nlinarith
    interval_cases b <;> try interval_cases a <;> omega

  have h_sum_expr : m + n = 8 * (a + b) := by
    clear * - h_step4 h_step5
    linarith

  have h_case_1 : a + b = 15 → m + n = 120 := by
    clear * - h_sum_expr
    intro a_1
    simp_all only [reduceMul, a, b]

  have h_case_2 : a + b = 9 → m + n = 72 := by
    clear * - h_sum_expr
    intro a_1
    simp_all only [reduceMul, a, b]

  have h_final : 72 ≤ m + n := by
    clear * - h_step_cases h_case_1 h_case_2
    simp_all only [a, b]
    (omega)

  exact h_final
