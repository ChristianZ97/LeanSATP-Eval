# Prover brief (DSP, Opus stage): prove one gap of a Lean 4 sketch

A DSP sketch restates each theorem of a thesis chapter in Lean 4 (with Mathlib) and replaces its proof by the
thesis's steps. A step that still needs proof work is a *gap*, written `prove_with [h₁, …]`: at the gap, the context
is cut down to the listed hypotheses (`clear * - h₁ …`). Earlier stages (an automatic prover and a tree search) did
not close your gap. Your task: write a Lean 4 proof of this one gap.

## What you write

- Your proof is pasted at the gap, right after `clear * - <hints>`. It must prove the goal shown below from the
  context shown below (the context after `clear`).
- Do not change the gap's statement or its hints.
- Do not use `sorry`, `admit` or `native_decide`. Do not add axioms, `set_option`, imports or declarations.
- You may use:
  - all of Mathlib;
  - the 32 public statements of `Sec2`: the statement skeleton below holds them with their docstrings (their proofs
    exist; you see only the statements);
  - the `Sec2.DSP` theorems that come before this theorem in the thesis order (named below; each has the same
    statement as its skeleton version).
- Do not use the theorem you are proving, or the theorems that come after it in the thesis order (named below), in
  either namespace.
- Names resolve as in the module (its `open` line and namespace are given below). Inside `Sec2.DSP`, a bare name
  resolves to the `Sec2.DSP` version when there is one, and to the `Sec2` version otherwise.

## How you submit

- You have no tools; do not call any. Each reply of yours is either one proof attempt or your final report.
- A proof attempt is exactly one fenced code block tagged `lean`, holding only the tactic proof (what follows
  `clear * - <hints>`, without `by`), followed by one sentence saying what the proof does.
- The coordinator compiles it in place: the module, this gap as `clear * - <hints>` and then your proof, every other
  gap `sorry`, the header `import Mathlib`, the module's imports, its `open` line, `set_option maxHeartbeats 0`, at
  most 600 seconds. It is accepted when Lean reports no error and the proof term built for this gap uses only the
  axioms propext, Classical.choice and Quot.sound.
- You get back `ACCEPTED`, or Lean's error messages verbatim, with positions counted in your code block (`proof:3:5`
  is line 3, column 5 of your block).
- Budget: 12 attempts or 60 minutes from this message, whichever comes first. A reply the coordinator cannot use
  (no `lean` block, or a forbidden word) is not an attempt.
- If you judge that the gap as written is false, or that its hints miss a hypothesis it needs, do not force a proof.
  Reply instead with a first line starting `CLAIM:`, then the reason and a counterexample or the missing hypothesis.
  The coordinator checks the claim. If it holds, the gap goes back to the sketch. If not, you get the check back and
  go on.

## Report (your final reply)

- After `ACCEPTED` nothing more is needed. Send a report when the budget is used up, or when you stop.
- First line: `<GAP> | NOT PROVED after N attempts: <one-line reason>`.
- Then 1–3 lines on what you tried.

## Warning cleaning (after assembly)

In the build of the assembled files, Lean's linters reported warnings in some accepted proofs. Each subagent whose
accepted proof had such warnings got the message below, in the same conversation. A revision was checked as above,
and in addition the gap had to be free of these warnings; at most 3 rounds, otherwise the accepted proof was kept.

````text
Your proof of this gap is accepted. Lean reports the linter warnings below for it. Please make
the proof clean:
- remove the tactics and the `first | … | …` alternatives that the linter says are never
  executed or do nothing;
- remove the unused simp arguments;
- replace deprecated names by the names Lean suggests.
Change nothing else, and do not restructure the proof. Reply with the whole revised proof in
one fenced lean block, as before.

Lean's warnings for your proof (positions as before: proof:L:C is line L, column C of your proof):

<the warnings Lean reports in this gap, verbatim>

Your current proof:

```lean
<the accepted proof>
```
````
