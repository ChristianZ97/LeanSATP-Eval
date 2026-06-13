import Mathlib
open BigOperators Real Nat Topology Rat
/-- Which of the following is equivalent to
$(2+3)(2^2+3^2)(2^4+3^4)(2^8+3^8)(2^{16}+3^{16})(2^{32}+3^{32})(2^{64}+3^{64})?$
$\textbf{(A)} ~3^{127} + 2^{127} \qquad\textbf{(B)} ~3^{127} + 2^{127} + 2 \cdot 3^{63} + 3 \cdot 2^{63} \qquad\textbf{(C)} ~3^{128}-2^{128} \qquad\textbf{(D)} ~3^{128} + 2^{128} \qquad\textbf{(E)} Show that it is \textbf{(C)} ~3^{128}-2^{128}.-/

theorem amc12a_2021_p9 : (∏ k in Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k)) = 3 ^ 128 - 2 ^ 128 := by

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
    (add unsafe 30% (by first | apply ultrafilterBasis_is_basis | rw [ultrafilterBasis_is_basis] | simp only [ultrafilterBasis_is_basis]))