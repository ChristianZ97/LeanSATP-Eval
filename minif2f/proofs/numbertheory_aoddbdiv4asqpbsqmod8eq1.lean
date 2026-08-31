import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem numbertheory_aoddbdiv4asqpbsqmod8eq1 (a : ℤ) (b : ℕ) (h₀ : Odd a) (h₁ : 4 ∣ b) :
    (a ^ 2 + b ^ 2) % 8 = 1 := by
  obtain ⟨k, hk⟩ := h₀
  obtain ⟨m, hm⟩ := h₁

  have h_step1 : a = 2 * k + 1 := by
    clear * - hk
    simp_all only

  have h_step2 : a ^ 2 = (2 * k + 1) ^ 2 := by
    clear * - h_step1
    simp_all only

  have h_step3 : a ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by
    clear * - h_step2
    simp_all only
    (linarith)

  have h_step4 : a ^ 2 = 4 * (k * (k + 1)) + 1 := by
    clear * - h_step3
    simp_all only [add_left_inj]
    (linarith)

  have h_step5 : ∃ n : ℤ, k * (k + 1) = 2 * n := by
    clear * -
    have := k * (k + 1)
    use (k * (k + 1)) / 2
    obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := Int.even_or_odd k <;> ring_nf <;> omega

  obtain ⟨n, hn⟩ := h_step5

  have h_step6 : a ^ 2 = 4 * (2 * n) + 1 := by
    clear * - h_step4 hn
    simp_all only

  have h_step7 : a ^ 2 = 8 * n + 1 := by
    clear * - h_step6
    simp_all only [add_left_inj]
    (linarith)

  have h_step8 : (b : ℤ) = 4 * (m : ℤ) := by
    clear * - hm
    subst hm
    simp_all only [Nat.cast_mul, Nat.cast_ofNat]

  have h_step9 : (b ^ 2 : ℤ) = (4 * (m : ℤ)) ^ 2 := by
    clear * - h_step8
    simp_all only

  have h_step10 : (b ^ 2 : ℤ) = 16 * (m ^ 2 : ℤ) := by
    clear * - h_step9
    simp_all only [Nat.cast_nonneg, ofNat_pos, mul_nonneg_iff_of_pos_left, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀]
    (linarith)

  have h_step11 : (b ^ 2 : ℤ) = 8 * (2 * (m ^ 2 : ℤ)) := by
    clear * - h_step10
    simp_all only
    (linarith)

  have h_step12 : (a ^ 2 + b ^ 2 : ℤ) = (8 * n + 1 : ℤ) + (8 * (2 * (m ^ 2 : ℤ))) := by
    clear * - h_step7 h_step11
    simp_all only

  have h_step13 : (a ^ 2 + b ^ 2 : ℤ) = 8 * (n + 2 * (m ^ 2 : ℤ)) + 1 := by
    clear * - h_step12
    simp_all only
    (linarith)

  have h_step14 : ∃ q : ℤ, a ^ 2 + b ^ 2 = 8 * q + 1 := by
    clear * - h_step13
    simp_all only [add_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq']

  have h_step15 : (a ^ 2 + b ^ 2) % 8 = 1 := by
    clear * - h_step14
    (omega)

  exact h_step15
