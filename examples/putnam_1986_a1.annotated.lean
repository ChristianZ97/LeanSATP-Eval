/-
putnam_1986_a1 (PutnamBench).  S = {x | x⁴ + 36 ≤ 13x²},  f x = x³ − 3x.
Show  IsGreatest {f x | x ∈ S} 18.  Each `have` is one sketch gap; the tag marks
which solver closed it.  [satp] = 0.2B SATP policy, [bfs] = BFS-Prover-V2-7B.
Verifies with `import Mathlib` alone.
-/
import Mathlib

set_option maxHeartbeats 0

abbrev putnam_1986_a1_solution : ℝ := 18
theorem putnam_1986_a1
    (S : Set ℝ) (f : ℝ → ℝ)
    (hS : S = {x : ℝ | x ^ 4 + 36 ≤ 13 * x ^ 2})
    (hf : f = fun x ↦ x ^ 3 - 3 * x) :
    IsGreatest
    {f x | x ∈ S}
    putnam_1986_a1_solution := by
  -- [bfs]  characterise S = [-3,-2] ∪ [2,3]
  have h1 : S = Set.Icc (-3) (-2) ∪ Set.Icc (2 : ℝ) 3 := by
    clear * - hS
    simp_all only
    ext a <;> norm_num
    aesop (add simp [or_comm])
    · obtain h | h := le_total a 0
      · right
        constructor <;> nlinarith [sq_nonneg (a ^ 2 - 4), sq_nonneg (a ^ 2 - 9)]
      ·
        exact
          Or.inl
            ⟨by nlinarith [sq_nonneg (a ^ 2 - 4), sq_nonneg (a ^ 2 - 9)], by
              nlinarith [sq_nonneg (a ^ 2 - 4), sq_nonneg (a ^ 2 - 9)]⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr left) (sub_nonneg.mpr right), sq_nonneg (a ^ 2 - 5)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr right) (sub_nonneg.mpr left), sq_nonneg (a ^ 2 - 5)]
  -- [satp]  unfold f x = x³ − 3x
  have h2 : ∀ x : ℝ, f x = x ^ 3 - 3 * x := by
    clear * - hf
    intro x
    subst hf
    simp_all only
  -- [satp]  deriv f x = 3x² − 3
  have h3 : ∀ x : ℝ, deriv f x = 3 * x ^ 2 - 3 := by
    clear * - hf
    intro x
    subst hf
    (ring_nf at *)
    simp_all only [differentiableAt_neg_iff, differentiableAt_id', differentiableAt_const, DifferentiableAt.mul,
      DifferentiableAt.pow, deriv_add, deriv.neg', deriv_mul, deriv_id'', one_mul, deriv_const', mul_zero, add_zero,
      deriv_pow'', Nat.cast_ofNat, Nat.reduceSub, mul_one]
    (nlinarith)
  -- [satp]  critical points ±1
  have h4 : deriv f 1 = 0 ∧ deriv f (-1) = 0 := by
    clear * - h3
    simp_all only [one_pow, mul_one, sub_self, even_two, Even.neg_pow, and_self]
  -- [satp]  ±1 ∉ S
  have h5 : (1 : ℝ) ∉ S ∧ (-1 : ℝ) ∉ S := by
    clear * - h1 h4
    subst h1
    simp_all only [Set.mem_union, Set.mem_Icc, Nat.not_ofNat_le_one, Nat.one_le_ofNat, and_true, or_false, not_and,
      not_le, neg_le_neg_iff, and_false, false_or]
    obtain ⟨left, right⟩ := h4
    apply And.intro
    · intro a
      (nlinarith)
    · intro a
      (nlinarith)
  -- [satp]  f(-3) = -18
  have h6 : f (-3) = -18 := by
    clear * - h2
    simp_all only [mul_neg, sub_neg_eq_add]
    (nlinarith)
  -- [satp]  f(-2) = -2
  have h7 : f (-2) = -2 := by
    clear * - h2
    simp_all only [mul_neg, sub_neg_eq_add]
    (nlinarith)
  -- [satp]  f(2) = 2
  have h8 : f 2 = 2 := by
    clear * - h2
    simp_all only
    (nlinarith)
  -- [satp]  f(3) = 18
  have h9 : f 3 = 18 := by
    clear * - h2
    simp_all only
    (nlinarith)
  -- [satp]  f(3) = solution
  have h10 : f 3 = putnam_1986_a1_solution := by
    clear * - h9
    simp_all only
  -- [satp]  3 ∈ S
  have h11 : 3 ∈ S := by
    clear * - h1
    subst h1
    simp_all only [Set.mem_union, Set.mem_Icc, neg_le_self_iff, Nat.ofNat_nonneg, true_and, le_refl, and_true]
    (norm_num [*] at *)
  -- [satp]  18 is attained
  have h12 : (putnam_1986_a1_solution : ℝ) ∈ {f x | x ∈ S} := by
    clear * - h10 h11
    simp_all only [Set.mem_setOf_eq]
    (bound )
  -- [bfs]  upper bound ∀ x ∈ S, f x ≤ 18
  have h13 : ∀ x ∈ S, f x ≤ putnam_1986_a1_solution := by
    clear * - h1 h2 h3 h5
    simp_all
    norm_num [putnam_1986_a1_solution]
    rintro x (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
  -- [bfs]  assemble IsGreatest
  have h14 : IsGreatest {f x | x ∈ S} putnam_1986_a1_solution := by
    clear * - h12 h13
    simp_all only [Set.mem_setOf_eq]
    constructor
    · simp_all only [Set.mem_setOf_eq]
    · rintro y ⟨z, hz1, hz2⟩
      simp only [← hz2, h13 z hz1]
  exact h14
