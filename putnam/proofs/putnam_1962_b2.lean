
import Mathlib
open MeasureTheory

set_option maxHeartbeats 0

theorem putnam_1962_b2
: ∃ f : ℝ → Set ℕ+, ∀ a b : ℝ, a < b → f a ⊂ f b := by
  have h_enum : ∃ e : ℕ+ ≃ ℚ, True := by
    clear * -
    aesop
    (add safe 1 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 80% (by ext))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 80% (by omega))
    (add unsafe 80% (by split))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by exfalso))
    (add unsafe 70% (by gcongr))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by positivity))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 40% (by first | apply Relation.ReflTransGen.single | rw [Relation.ReflTransGen.single] | simp only [Relation.ReflTransGen.single]))
    (add unsafe 10% (by first | apply MvPowerSeries.mul_invOfUnit | rw [MvPowerSeries.mul_invOfUnit] | simp only [MvPowerSeries.mul_invOfUnit]))
    (add unsafe 10% (by first | apply SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint | rw [SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint] | simp only [SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint]))
    (add unsafe 10% (by first | apply rfl | rw [rfl] | simp only [rfl]))

  obtain ⟨e, _⟩ := h_enum
  let q : ℕ+ → ℚ := e
  let f : ℝ → Set ℕ+ := fun x => {n : ℕ+ | (q n : ℝ) < x}
  use f
  intro a b hab
  have h_exists_k : ∃ k : ℕ+, (a : ℝ) < (q k : ℝ) ∧ (q k : ℝ) < b := by
    clear * - hab
    simp_all only [q]
    have a_rat : ∃ n : ℤ, a < (n : ℝ)
    · obtain ⟨n, hn⟩ := exists_nat_gt b
      exact ⟨n, hab.trans hn⟩
    · obtain ⟨m, hm⟩ := a_rat
      obtain ⟨n, hn⟩ := exists_rat_btwn hab
      exact ⟨e.symm n, by simpa using hn⟩

  obtain ⟨k, hk1, hk2⟩ := h_exists_k
  have h_k_in_fb : k ∈ f b := by
    clear * - hk2
    simp_all only [Set.mem_setOf_eq, q, f]

  have h_k_not_in_fa : k ∉ f a := by
    clear * - hk1
    simp_all only [Set.mem_setOf_eq, not_lt, q, f]
    (nlinarith)

  simp_all only [Set.mem_setOf_eq, not_lt, q, f]
  rw [lt_iff_le_and_ne] at hk2
  simp_all only [ne_eq]
  simp only [Set.ssubset_def, Set.mem_setOf_eq, h_k_not_in_fa, if_false, imp_true_iff]
  simp_all
  constructor
  · intro m hm
    linarith
  · use k
    simp_all only [and_true]
    exact hk2.1.lt_of_ne (by exact hk2.2)
