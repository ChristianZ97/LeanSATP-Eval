import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

syntax "∑ " ident " in " term ", " term:67 : term
syntax "∏ " ident " in " term ", " term:67 : term
macro_rules
  | `(∑ $x:ident in $s, $f) => `(∑ $x ∈ $s, $f)
  | `(∏ $x:ident in $s, $f) => `(∏ $x ∈ $s, $f)

theorem mathd_algebra_209 (σ : Equiv ℝ ℝ) (h₀ : σ.2 2 = 10) (h₁ : σ.2 10 = 1) (h₂ : σ.2 1 = 2) :
    σ.1 (σ.1 10) = 1 := by
  have h_step1 : σ.1 (σ.2 2) = σ.1 10 := by
    clear * - h₀
    simp_all only [Equiv.invFun_as_coe, Equiv.toFun_as_coe]

  have h_step2 : (2 : ℝ) = σ.1 10 := by
    clear * - h_step1
    simp_all only [Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply]

  have h_step3 : σ.1 (σ.1 10) = σ.1 2 := by
    clear * - h_step2
    simp_all only [Equiv.toFun_as_coe]

  have h_step4 : σ.1 (σ.2 1) = σ.1 2 := by
    clear * - h₂
    simp_all only [Equiv.invFun_as_coe, Equiv.toFun_as_coe]

  have h_step5 : (1 : ℝ) = σ.1 2 := by
    clear * - h_step4
    simp_all only [Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply]

  have h_step6 : σ.1 (σ.1 10) = 1 := by
    clear * - h_step3 h_step5
    simp_all only [Equiv.toFun_as_coe, EmbeddingLike.apply_eq_iff_eq]

  exact h_step6
