# Generator brief (DSP): construct the arguments t_C for one lemma rule of satp's configuration A

satp is a learned policy that emits an `aesop` configuration A for a Lean goal. A is a list of rules
`(add τ ρ (by W[ℓ]))`; in a lemma rule the wrapper W (e.g. `grind only [{L}]`, `nlinarith [{L}]`) holds the lemma
name ℓ alone, because the policy can only select. On your gap A fails: aesop spends its 200000 heartbeats without a
proof.

Your task: make A prove the gap by giving arguments to ONE lemma rule that A's search actually runs, in place:
`(τ, ρ, W, ℓ) → (τ, ρ, W, ℓ t_C)`. Rule type, priority, position, wrapper and lemma stay; the rest of A stays. This is
the protocol of journal §5.5: the new configuration A′ differs from A by one generative rule.

## Your input

Below this brief: the goal, A with line numbers, the editable rules (LINE, type and priority, wrapper, lemma, `#check`
signature, how often A runs the rule), the goal states those rules see inside A (after A's normalization), and the
context names. That is everything you get.

## How you submit candidates

- You have no tools; do not call any. Each reply of yours is either one round of candidates or your final report.
- A round is one fenced code block tagged `candidates`, with 1–8 lines `LINE | ℓ args`. In a list wrapper such as
  `grind only [{L}]` you may give several instances of the same ℓ, comma-separated:
  `22 | sq_nonneg (a - b), sq_nonneg (a + b)`.
- The coordinator runs the check script on your block and sends you its output verbatim. You have 5 rounds, or
  30 minutes from your first round; the script enforces both. A block the script rejects (`REJECT: …`) is not a round:
  fix it and send it again.
- ✓ means A′ proves the gap where it stands in the sketch: the gap's own context after `clear * - <hints>` (the goal
  below), the sketch's other gaps `sorry`, A′ with 200000 heartbeats counted from its start (the budget satp? gives
  each call), no `sorry` in the proof A′ builds, only the axioms propext, Classical.choice, Quot.sound. ✗ comes with
  the first Lean error.
- A ✓ then goes through journal §5.5's two checks, run by the script:
  1. Instances that are not needed are dropped, until dropping any one of the rest fails.
  2. The counterpart replaces every constructed argument, numerals included, with each context name, and puts every
     well-typed result into the same rule. If no context name fits (an empty counterpart), the counterpart is the
     instance with the constructed arguments left out and its context names kept, positional ones as `_` (user
     ruling, 2026-11-01): `Finset.mul_sum Finset.univ g c` → `Finset.mul_sum _ g c`.
  - If the counterpart also proves the gap, selection among the context's names suffices (picking a name the
    context already has is not a construction): the script prints `NOT COUNTED` and you go on. Otherwise it prints
    `SOLVED`, which ends the task.

## Rules (the script rejects anything else)

- **Terms only:** no `by`, `;`, `<;>`, `sorry`, `admit`, `native_decide`, `fun`, `λ`, `·`, `=>`, `match`, recursors
  (`.rec`, `.recOn`, `.casesOn`), no line breaks.
- **No function combinators** (user ruling, 2026-11-01): `∘`, `Function.comp`, `Function.swap`, `flip`,
  `Function.onFun`, `Function.eval`, `Function.const`, `Function.curry`, `Function.uncurry` spell a lambda without
  `fun` and count as the `fun` ban. The script matches these names after Lean resolves them, so `open Function` does
  not help.
- **No other lemma:**
  - On a hypothesis only numeric projections are allowed (`h.1`, `h.2`); `h.le`, `h.trans` call lemmas and are
    rejected.
  - Every other name that is not a context name must not be a lemma, i.e. its type must not be a proposition; Lean
    decides. Functions such as `Real.log`, `Real.sqrt`, `max`, `Nat.ceil`, `id` are fine; theorems such as
    `congrArg` or `sq_nonneg` are rejected.
  - Allowed: numerals, arithmetic, applications of context names, type ascriptions `(2 : ℝ)`, named arguments
    `(x := t)`, `if … then … else`.
- **Same lemma:** the lemma stays the rule's own ℓ.

## How to think (lessons from journal §5.5)

- **Proof first:** work out the human proof first. Ask which instance of ℓ is the key fact:
  - a square to complete;
  - ℓ at a computed point;
  - a factorization;
  - a bound at the right value.

  Then write exactly that instance.
- **How `grind only [ℓ args]` uses your instance:**
  - A fully instantiated fact, or an iff, is used directly.
  - An instance with unfilled hypotheses becomes a pattern that fires only if its conclusion's term already occurs.
    So give the arguments that make the hypotheses easy, or name the implicit arguments: `ℓ (x := 11)`.
- **Linear arithmetic:** `grind` does linear arithmetic over products of atoms; it does not multiply hypotheses. The
  fact you add must make the goal follow linearly from what it has.
- **`rw [ℓ args]`:** rewrites with the instantiated equation, so it must match a subterm of the goal the rule sees.
- **The goal the rule sees:** A normalizes the goal before lemma rules run. Read "Goal states these rules see inside
  A" below; the rule sees that goal, not the original statement.
- **Use every round:** often several instances in one rule are needed. Use all 8 candidates per round, vary rules
  and instances, and read each failure before the next round.
- **Stopping early:** run at least one round first. Stop before 5 rounds only if you can argue that no argument can
  work, for example that no editable lemma mentions a function the proof needs, so that every instance stays true
  under a reinterpretation that falsifies the goal. Put that argument in your report.

## Report (your final reply, concise)

- Send it after `SOLVED`, after the budget is used up, or when you stop early.
- First line: `<GAP> | SOLVED round R line L: <instances>` or `<GAP> | NOT SOLVED after R rounds: <one-line reason>`.
- Then 1–3 lines on what you tried.
