import Mathlib
open BigOperators Real Nat Topology Rat
/-- Find the remainder when $1 + 2 + 2^2 + 2^3 + \dots + 2^{100}$ is divided by 7. Show that it is 3.-/

theorem mathd_numbertheory_127 : (∑ k in Finset.range 101, 2 ^ k) % 7 = 3 := by

    aesop (config := {
    maxNormIterations       := 120
    maxGoals                := 64
  })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by linarith))
    (add unsafe 70% (by bound))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 30% (by first | apply Ioc_mem_nhdsWithin_Iic | rw [Ioc_mem_nhdsWithin_Iic] | simp only [Ioc_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply Ioo_mem_nhdsWithin_Iic | rw [Ioo_mem_nhdsWithin_Iic] | simp only [Ioo_mem_nhdsWithin_Iic]))
    (add unsafe 30% (by first | apply Quaternion.imI_nnratCast | rw [Quaternion.imI_nnratCast] | simp only [Quaternion.imI_nnratCast]))
    (add unsafe 30% (by first | apply Quaternion.imK_nnratCast | rw [Quaternion.imK_nnratCast] | simp only [Quaternion.imK_nnratCast]))
    (add unsafe 30% (by first | apply Submodule.coe_sub | rw [Submodule.coe_sub] | simp only [Submodule.coe_sub]))
    (add unsafe 30% (by first | apply Zspan.quotientEquiv_apply_mk | rw [Zspan.quotientEquiv_apply_mk] | simp only [Zspan.quotientEquiv_apply_mk]))