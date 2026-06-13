import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_numbertheory_552 (f g h : ℕ+ → ℕ) (h₀ : ∀ x, f x = 12 * x + 7)
    (h₁ : ∀ x, g x = 5 * x + 2) (h₂ : ∀ x, h x = Nat.gcd (f x) (g x)) (h₃ : Fintype (Set.range h)) :
    (∑ k in (Set.range h).toFinset, k) = 12 := by
  have h_linear_combination : ∀ (x : ℕ+), 5 * f x - 12 * g x = 11 := by
    clear * - h₀ h₁
    intro x
    simp_all only
    (omega)

  have h_gcd_divides_diff : ∀ (x : ℕ+), h x ∣ (5 * f x - 12 * g x) := by
    clear * - h₂
    simp_all only
    intro x
    have := Nat.gcd_dvd (f x) (g x)
    exact dvd_sub' (this.1.mul_left _) (this.2.mul_left _)

  have h_gcd_divides_11 : ∀ (x : ℕ+), h x ∣ 11 := by
    clear * - h_linear_combination h_gcd_divides_diff
    intro x
    simp_all only

  have h_range_subset : Set.range h ⊆ ({1, 11} : Set ℕ) := by
    clear * - h_gcd_divides_11
    rintro x ⟨a, ha⟩
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hx := h_gcd_divides_11 a
    simp_all only
    rw [Nat.dvd_prime (by decide)] at hx <;> aesop

  have h_f_4 : f (4 : ℕ+) = 55 := by
    clear * - h₀
    simp_all only [PNat.val_ofNat, reduceMul, reduceAdd]

  have h_g_4 : g (4 : ℕ+) = 22 := by
    clear * - h₁
    simp_all only [PNat.val_ofNat, reduceMul, reduceAdd]

  have h_h_4 : h (4 : ℕ+) = 11 := by
    clear * - h₂ h_f_4 h_g_4
    simp_all only [reduceGcd]

  have h_f_1 : f (1 : ℕ+) = 19 := by
    clear * - h₀
    simp_all only [PNat.val_ofNat, mul_one, reduceAdd]

  have h_g_1 : g (1 : ℕ+) = 7 := by
    clear * - h₁
    simp_all only [PNat.val_ofNat, mul_one, reduceAdd]

  have h_h_1 : h (1 : ℕ+) = 1 := by
    clear * - h₂ h_f_1 h_g_1
    simp_all only [reduceGcd]

  have h_11_in_range : 11 ∈ Set.range h := by
    clear * - h_h_4
    simp_all only [Set.mem_range]
    (bound )

  have h_1_in_range : 1 ∈ Set.range h := by
    clear * - h_h_1
    simp_all only [Set.mem_range]
    (bound )

  have h_range_eq : Set.range h = ({1, 11} : Set ℕ) := by
    clear * - h_range_subset h_11_in_range h_1_in_range
    simp_all only [Set.mem_range]
    obtain ⟨w, h_1⟩ := h_11_in_range
    obtain ⟨w_1, h_2⟩ := h_1_in_range
    ext x : 1
    simp_all only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    apply Iff.intro
    · intro a
      obtain ⟨w_2, h_3⟩ := a
      subst h_3
      (bound )
    · intro a
      cases a with
      | inl h_3 =>
        subst h_3
        (bound )
      | inr h_4 =>
        subst h_4
        (bound )

  have h_finset_eq : (Set.range h).toFinset = ({1, 11} : Finset ℕ) := by
    clear * - h_range_eq
    simp_all only [Set.toFinset_insert, Set.toFinset_singleton]

  have h_sum_calculation : ∑ k in ({1, 11} : Finset ℕ), k = 12 := by
    clear * -
    simp_all only [Finset.mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton,
        reduceAdd]

  have h_main_goal : ∑ k in (Set.range h).toFinset, k = 12 := by
    clear * - h_finset_eq h_sum_calculation
    simp_all only [Finset.mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton,
        reduceAdd]

  exact h_main_goal
