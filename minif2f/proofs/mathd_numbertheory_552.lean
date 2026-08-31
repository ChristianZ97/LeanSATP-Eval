import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_numbertheory_552 (f g h : ℕ+ → ℕ) (h₀ : ∀ x, f x = 12 * x + 7)
  (h₁ : ∀ x, g x = 5 * x + 2) (h₂ : ∀ x, h x = Nat.gcd (f x) (g x)) (h₃ : Fintype (Set.range h)) :
  (∑ k in (Set.range h).toFinset, k) = 12 := by
  have h_ineq : ∀ (x : ℕ+), (5 : ℕ) * (f x) ≥ (12 : ℕ) * (g x) := by
    clear * - h₀ h₁
    simp_all [-mul_comm]
    exact fun k => by linarith

  have h_lin_comb : ∀ (x : ℕ+), (5 : ℕ) * (f x) - (12 : ℕ) * (g x) = 11 := by
    clear * - h₀ h₁ h_ineq
    simp only [ge_iff_le] at *
    (bound )
    (ring_nf at *)
    (simp_all [Nat.sub_add_cancel])
    (omega)

  have h_div_f : ∀ (x : ℕ+), h x ∣ f x := by
    clear * - h₂
    simp [h₂, Nat.gcd_dvd_left]

  have h_div_g : ∀ (x : ℕ+), h x ∣ g x := by
    clear * - h₂
    intro c
    simp_rw [h₂, Nat.gcd_dvd_right]

  have h_div_lin : ∀ (x : ℕ+), h x ∣ (5 * f x - 12 * g x) := by
    clear * - h_div_f h_div_g h_ineq
    intro c
    have hcf := h_div_f c
    have hdvd := h_div_g c
    exact dvd_sub (hcf.mul_left _) (hdvd.mul_left _)

  have h_div_11 : ∀ (x : ℕ+), h x ∣ 11 := by
    clear * - h_div_lin h_lin_comb
    intro x
    simp_all only

  have h_range_subset : Set.range h ⊆ ({1, 11} : Set ℕ) := by
    clear * - h_div_11 h₀ h₁
    intro y hy
    aesop  (add simp [Set.mem_range])
    have hww := h_div_11 w
    classical
    have : h w ≤ 11 := Nat.le_of_dvd (by norm_num) hww
    interval_cases h w <;> simp_all (config := { decide := true }) [h₁, h₀]

  have h_case_1 : h (1 : ℕ+) = 1 := by
    clear * - h₀ h₁ h₂
    (simp_all)

  have h_1_in_range : 1 ∈ Set.range h := by
    clear * - h_case_1
    simp only [Set.mem_range] at *
    (bound )

  have h_case_4 : h (4 : ℕ+) = 11 := by
    clear * - h₀ h₁ h₂
    simp_all only [PNat.val_ofNat, reduceMul, reduceAdd, reduceGcd]

  have h_11_in_range : 11 ∈ Set.range h := by
    clear * - h_case_4
    simp only [Set.mem_range] at *
    (bound )

  have h_range_eq : Set.range h = {1, 11} := by
    apply Set.Subset.antisymm
    · exact h_range_subset
    · -- Show {1, 11} ⊆ range h
      clear * - h_1_in_range h_11_in_range
      simp_all only [Set.mem_range]
      (ring_nf at *)
      obtain ⟨w, h_1⟩ := h_1_in_range
      obtain ⟨w_1, h_2⟩ := h_11_in_range
      (simp only [Set.insert_subset_iff])
      simp_all only [Set.mem_range, Set.singleton_subset_iff]
      (grind only [Set.range_subset_iff])

  have h_sum_calc : (∑ k in (Set.range h).toFinset, k) = 1 + 11 := by
    simp_all only
    (bound )

  have h_arith : (1 : ℕ) + 11 = 12 := by
    clear * -
    simp only [reduceAdd] at *

  exact h_sum_calc
