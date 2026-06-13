/-
mathd_algebra_302 (MiniF2F-test) — an e2e win: satp closed the whole theorem in one
`aesop` call. Vanilla `aesop` (no added configuration) does NOT close this goal; the
emitted config below does.

The emission is goal-conditioned — unlike the static backbone it raises
`maxNormIterations` to 160, sets `maxGoals := 64`, and adds Complex-specific lemmas
(`Complex.I_mul_I`, i.e. i·i = −1; `Complex.inv_I`; `Complex.exp_pi_mul_I`).

aesop's `Try this:` reduces it to a short Complex-arithmetic proof (see
proofs/mathd_algebra_302.lean):

    simp_all only [one_div]; ring
    simp_all only [Complex.I_sq, one_div, neg_mul, one_mul]; ring   -- uses i² = −1

Below is the emitted form, verified as-is.
-/
import Mathlib
open BigOperators Real Nat Topology Rat

theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by

    aesop (config := {
    maxNormIterations       := 160
    maxGoals                := 64
  })
    (add safe 1 (by ring))
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by ring_nf at *))
    (add unsafe 100% (by simp_all))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by ext))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by interval_cases))
    (add unsafe 90% (by linarith))
    (add unsafe 90% (by norm_num [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 70% (by nlinarith))
    (add unsafe 70% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by positivity))
    (add unsafe 40% (by first | apply Complex.exp_pi_mul_I | rw [Complex.exp_pi_mul_I] | simp only [Complex.exp_pi_mul_I]))
    (add unsafe 30% (by first | apply Complex.I_mul_I | rw [Complex.I_mul_I] | simp only [Complex.I_mul_I]))
    (add unsafe 30% (by first | apply Complex.inv_I | rw [Complex.inv_I] | simp only [Complex.inv_I]))
