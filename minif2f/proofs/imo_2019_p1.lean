import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem imo_2019_p1 (f : ℤ → ℤ) :
  (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔ ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  constructor
  · intro h_eq
    let c := f 0
    have h_step3 : f (f 0) = 3 * c := by
      clear * - h_eq
      have h0 := h_eq 0 0
      simp_all [c] <;> omega

    have h_step4 : ∀ a, f (2 * a) + 2 * c = f (f a) := by
      clear * - h_eq
      simp_all only [add_zero, implies_true, c]

    have h_step5 : ∀ b, c + 2 * f b = f (f b) := by
      clear * - h_eq
      intro b
      have h := h_eq 0 b
      aesop  (add simp [c])

    have h_step6 : ∀ a, f (2 * a) + 2 * c = c + 2 * f a := by
      clear * - h_step4 h_step5
      simp_all only [implies_true, c]

    have h_step9 : ∀ a, f (2 * a) = 2 * f a - c := by
      clear * - h_step6
      simp_all only [c]
      (grind only [two_mul])

    have h_step10 : ∀ x, f (f x) = 2 * f x + c := by
      clear * - h_step5
      simp_all only [c]
      (grind only [two_mul])

    have h_step14 : ∀ a b, 2 * f (a + b) = 2 * f a + 2 * f b - 2 * c := by
      clear * - h_eq h_step9 h_step10
      intro a b
      (grind only [two_mul])

    have h_step15 : ∀ a b, f (a + b) = f a + f b - c := by
      clear * - h_step14
      intro a b
      simp_all only [c]
      (grind only [two_mul])

    let g := fun x ↦ f x - c
    have h_step18 : ∀ a b, g (a + b) = g a + g b := by
      clear * - h_step15
      simp_all only [c, g]
      (omega)

    have h_step19 : ∃ k : ℤ, ∀ x, g x = k * x := by
      clear * - h_step18
      let k := g 1
      use k
      intro z
      induction z
      · simp [mul_zero]
        specialize h_step18 0 0 <;> simp_all
      · simp_all [add_mul, mul_add, h_step18] <;> nlinarith
      · simp_all [sub_eq_add_neg, h_step18]
        linarith [show (g (-1) : ℤ) = -k by have h := h_step18 (-1) 1; simp [sub_eq_add_neg] at h; linarith]

    obtain ⟨k, hk⟩ := h_step19
    have h_step20 : ∀ x, f x = k * x + c := by
      clear * - hk
      simp_all only [g, c]
      (ring_nf at *)
      (simp_all [eq_comm])

    have h_step25 : 2 * k - k ^ 2 = 0 := by
      clear * - h_eq h_step20
      have h1 := h_eq 0 0
      have h2 := h_eq 1 0
      simp_all [h_step20, mul_add]
      nlinarith [sq_nonneg (k - 2), sq_nonneg (k + 1)]

    have h_step26 : 2 * c - k * c = 0 := by
      clear * - h_eq h_step20
      have h₁ := h_eq 0 (0)
      ring_nf at h₁ <;> simp_all
      nlinarith [h_eq 1 0, h_eq 0 1, h_eq 1 1, h_eq (-1) 1]

    have h_step27 : k = 0 ∨ k = 2 := by
      clear * - h_step25
      classical
      have : k ≤ 2 := by nlinarith
      have : k ≥ 0 := by nlinarith
      interval_cases k <;> simp_all

    cases h_step27 with
    | inl h_k0 =>
      have h_c0 : c = 0 := by
        clear * - h_step26 h_k0
        subst h_k0
        simp_all only [zero_mul, sub_zero, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or, c]

      have h_sol_1 : ∀ z, f z = 0 := by
        clear * - h_step20 h_c0 h_k0
        simp_all only [zero_mul, zero_add, implies_true, c]

      exact λ z => Or.inl (h_sol_1 z)

    | inr h_k2 =>
      have h_sol_2 : ∃ c', ∀ z, f z = 2 * z + c' := by
        clear * - h_step20 h_k2
        simp [h_k2, h_step20]

      obtain ⟨c'', hc''⟩ := h_sol_2
      exact fun z => Or.inr ⟨c'', hc''⟩

  · -- Reverse direction
    intro h_sol
    intro a b
    (grind only [two_mul])
