import Mathlib

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

theorem mathd_algebra_209 (σ : Equiv ℝ ℝ) (h₀ : σ.2 2 = 10) (h₁ : σ.2 10 = 1) (h₂ : σ.2 1 = 2) :
    σ.1 (σ.1 10) = 1 := by
  simp_all only [Equiv.invFun_as_coe, Equiv.toFun_as_coe]
  let h := h₁
  have k := h₂
  simp_all only
  simp [← h₀, ← k, Equiv.apply_symm_apply]
