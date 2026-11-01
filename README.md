# LeanSATP-Eval

Lean 4 proofs from a DSP+ pipeline; subgoals closed by an SATP→BFS cascade.
Every proof compiles standalone with `lake env lean` on stock Mathlib — no
prover server, no REPL, no fork-only tactics.

This branch uses the **v4.27 SATP checkpoint** in a Lean `v4.27.0` environment.

| Benchmark | Proved | Published |
|---|---|---|
| MiniF2F-Test (244) | **188** (77.0%) | 188 |
| ProofNet#-Test (186) | **56** (30.1%) | 53 |
| PutnamBench (672) | **42** (6.3%) | 42 |

Each row is **one run**, not a union or an intersection across runs — see
[Run selection](#run-selection).

## Thesis Chapter 2

[`thesis_ch2/`](thesis_ch2/README.md) formalizes Chapter 2 of the SATP thesis (Section 2 of the journal
version) in Lean 4 on stock Mathlib: zero `sorry`, axioms within the allowlist below. It is not a DSP+
run. The proofs were written by Claude Opus 5.5 agents with Lean in the loop. Afterwards they were
broken down into 137 single-step leaf lemmas to show which steps `satp` can close:

| Leaves | satp policy infer | satp + generative rule | bfsaesop | Opus 5.5 |
|---|---|---|---|---|
| 137 | 73 | 5 | 37 | 22 |

A second version, [`thesis_ch2/dsp/`](thesis_ch2/dsp/README.md), follows the thesis text instead
(Draft–Sketch–Prove). Every step of the informal proofs of Section 2.2 is one `have` in a sketch
written without access to the proofs above. Each gap goes to `satp`, the generative rule,
`bfsaesop` and, as a fallback, Opus 5.5, in that order:

| Gaps | satp | satp + generative rule | bfsaesop | Opus 5.5 |
|---|---|---|---|---|
| 62 | 17 | 0 | 16 | 29 |

## Pipeline

[DSP+][dspplus] three stages:

1. Draft — an LLM writes an informal proof.
2. Sketch — the same LLM formalizes it into Lean 4 with a `sorry` per subgoal.
3. Prove — each `sorry` is closed by the `satpbfsaesop` cascade: the 0.2B
   [LeanSATP][leansatp] v4.27 policy emits one `aesop` config per goal state;
   gaps it misses escalate to BFS-Prover-V2-7B.

Drafter & sketcher: [Intel/Qwen3.6-27B-int4-AutoRound][q36].

## Layout

```
<benchmark>/proofs/<problem>.lean   the proof
<benchmark>/PINS.txt               run id, manifest sha256, gate, exclusions
```

One view per proof, unlike the v2 branch's two-way split: subgoals SATP closed
keep the `aesop (config := …) (add …)` block it emitted (176 of the 188 MiniF2F
files contain one), subgoals BFS closed carry the tactic sequence it found.

`PINS.txt` names the exact run and manifest each folder was cut from, and lists
every problem that was proved but not published, by name.

## Run selection

The four `satpbfsaesop` runs of each band differ only by prover sampling, so a
single run has to be chosen. Per benchmark:

- **MiniF2F** — band was 183 / 183 / **188** / 183. Run 3, unambiguously.
- **ProofNet#** — band was **56** / **56** / 55 / 55: runs 1 and 2 tie, sharing
  54 problems and holding 2 unique each. Broken by which run's unique problems
  lean harder on SATP, measured as SATP's share of the closed subgoals in the
  winning attempt: run 2 scores 78.9% (15 SATP / 4 BFS, both problems
  SATP-dominant) against run 1's 53.8% (7 / 6, one of the two closed purely by
  BFS). **Run 2.** The tie-break is a declared convention, not a measurement of
  which run is better.
- **PutnamBench** — a single run, no band.

## Verify

```bash
git clone https://github.com/ChristianZ97/LeanSATP
cd LeanSATP && ./setup.sh
lake env lean /path/to/minif2f/proofs/mathd_algebra_478.lean
```

Environment — `LeanSATP/deps/.pins`, in that file's field order:

```
toolchain    leanprover/lean4:v4.27.0
aesop        cb837cc26236ada03c81837bebe0acd9c70ced7d   (+ bfsScore patch)
LeanCopilot  v4.27.0
mathlib      a3a10db0e9d66acbebf76c5e6a135066525ac900
```

The environment edits no `Mathlib/*.lean`. The aesop fork adds a `bfsScore`
option that defaults to `false`, so these proofs do not depend on it.

Publishing gate, applied per file: standalone compile, then `#print axioms` on
the theorem with an allowlist of `propext`, `Classical.choice`, `Quot.sound`.

## Notes

- **`native_decide` — 5 of the 188 MiniF2F proofs** (`amc12_2001_p5`,
  `amc12a_2020_p4`, `mathd_algebra_170`, `mathd_numbertheory_353`,
  `mathd_numbertheory_427`) close a subgoal with a BFS-found `native_decide`,
  so they additionally depend on `Lean.ofReduceBool` and
  `Lean.trustCompiler` — i.e. on the compiler, not only on the kernel. They are
  published because the tactic is BFS's own output, but they are the reason the
  MiniF2F row is not uniformly kernel-checked.
- **ProofNet publishes 53 of 56.** `Axler_exercise_6_3`, `Axler_exercise_5_1`
  and `Ireland-Rosen_exercise_1_30` were proved in-run but their standalone
  reconstruction does not compile, so the gate rejected them. The proved count
  is the run's; the published count is what survives independent checking.
- **The MiniF2F row is not comparable to the v2 branch's 192.** This branch
  evaluates `minif2f-satp-v4.27`, the [google-deepmind/formal-conjectures][gdm]
  revision, where 74 of the 244 test statements differ verbatim from the
  statements v2 was scored on. The header of each MiniF2F proof vendors that
  revision's `answer()` term elaborator and `Real.nthRoot` verbatim (Apache-2.0,
  `@f564f8d7`), which those statements need.
- **ProofNet# is the EMNLP 2025 corrected release, test split only** (186
  problems). The validation split is excluded as training-contaminated.
- ProofNet and PutnamBench proofs carry the run's file-level
  `set_option maxHeartbeats 0`, left untouched as a run artifact. It relaxes a
  time limit; it does not weaken the kernel check.

[dspplus]: https://github.com/microsoft/DSP-Plus
[leansatp]: https://github.com/ChristianZ97/LeanSATP
[q36]: https://huggingface.co/Intel/Qwen3.6-27B-int4-AutoRound
[gdm]: https://github.com/google-deepmind/formal-conjectures
