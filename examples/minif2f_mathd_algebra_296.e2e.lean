/-
mathd_algebra_296 (MiniF2F-test) — an e2e win: SATP closed the whole theorem in one
`aesop` call, with no sketch and no subgoals. The block below is exactly what the
0.2B policy emitted for this goal. It is goal-conditioned and unlike the common
backbone config: the options are `maxGoals := 64, enableUnfold := false` (no
`maxNormIterations`), and the rule list is led by abs/integer lemmas (`abs_pow`,
`abs_mul`, `Nat.abs_cast`, …) plus `split` / `exfalso` / `interval_cases`.

aesop's `Try this:` distils the entire 22-rule search to one line — the proof in
proofs/mathd_algebra_296.lean:

    simp_all only [Int.reduceSub, Int.reduceAdd, Int.reduceMul, Int.reducePow,
                   abs_neg, abs_ofNat]

The goal is pure integer-literal reduction; none of the emitted rules are needed.
Below is the emitted form, verified as-is.
-/
import Mathlib
open BigOperators Real Nat Topology Rat

theorem mathd_algebra_296 : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by

    aesop (config := {
    maxGoals                := 64
    enableUnfold            := false
  })
    (add safe 4 (by field_simp))
    (add safe 4 (by push_neg))
    (add unsafe 100% (by nlinarith))
    (add unsafe 100% (by ring_nf))
    (add unsafe 100% (by split))
    (add unsafe 90% (by bound))
    (add unsafe 90% (by exfalso))
    (add unsafe 90% (by field_simp [*] at *))
    (add unsafe 90% (by simp))
    (add unsafe 80% (by gcongr))
    (add unsafe 80% (by interval_cases))
    (add unsafe 80% (by linarith))
    (add unsafe 80% (by norm_cast at *))
    (add unsafe 70% (by omega))
    (add unsafe 70% (by ring_nf at *))
    (add unsafe 40% (by first | apply abs_pow | rw [abs_pow] | simp only [abs_pow]))
    (add unsafe 40% (by first | apply mabs_of_one_le | rw [mabs_of_one_le] | simp only [mabs_of_one_le]))
    (add unsafe 40% (by first | apply one_le_mabs | rw [one_le_mabs] | simp only [one_le_mabs]))
    (add unsafe 30% (by first | apply abs_mul | rw [abs_mul] | simp only [abs_mul]))
    (add unsafe 30% (by first | apply mabs_of_one_lt | rw [mabs_of_one_lt] | simp only [mabs_of_one_lt]))
    (add unsafe 10% (by first | apply Nat.abs_cast | rw [Nat.abs_cast] | simp only [Nat.abs_cast]))
    (add unsafe 10% (by first | apply abs_one | rw [abs_one] | simp only [abs_one]))
