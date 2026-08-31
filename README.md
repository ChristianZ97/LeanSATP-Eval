# LeanSATP-Eval

> This branch preserves the v1 (paper) proof exhibits. The current release lives on [`main`](https://github.com/ChristianZ97/LeanSATP-Eval).

Lean 4 proofs from a DSP+ pipeline; subgoals closed by an SATP→BFS cascade.
All proofs compile with `lake env lean` on stock Mathlib, no prover server.

| Benchmark | Proved |
|---|---|
| MiniF2F-Test | 77.5% (189 / 244) |
| PutnamBench | 27 / 672 |

`#print axioms` on each proof: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## Pipeline

[DSP+][dspplus] three stages:

1. Draft — an LLM writes an informal proof.
2. Sketch — the same LLM formalizes it into Lean 4 with a `sorry` per subgoal.
3. Prove — each `sorry` is closed by the `satpbfsaesop4x` cascade: the 0.2B
   [LeanSATP][leansatp] policy emits one `aesop` config; gaps it misses go to
   BFS-Prover-V2-7B, up to ×4.

Drafter & Sketcher:

| Benchmark | Model |
|---|---|
| MiniF2F-Test | [Qwen3.5-27B-FP8][q35] |
| PutnamBench | [Qwen3.6-27B-FP8][q36] |

## Layout

```
minif2f/proofs/<p>.lean               minimized tactics
minif2f/proofs_aesop_config/<p>.lean  same proof, SATP's emitted aesop config
putnam/ …                             same two views
examples/                             one annotated proof per benchmark
```

`proofs/` is the minimized form (aesop `Try this:`). `proofs_aesop_config/` keeps the
`aesop (config := …) (add …)` block SATP emitted, e.g.
`minif2f/proofs_aesop_config/aime_1990_p4.lean`. `examples/` tags each `have` `[satp]`
or `[bfs]`; see `examples/README.md`.

## Verify

Built and checked in the [LeanSATP][leansatp] environment:

```bash
git clone --branch legacy https://github.com/ChristianZ97/LeanSATP
lake env lean /path/to/minif2f/proofs/amc12a_2002_p6.lean
```

Environment: lean4 `v4.17.0-rc1`, Mathlib `c3492e1786`, stock aesop. The build fork
changes no `Mathlib/*.lean` files; the proofs use no fork-only aesop options.

## Notes

- Some BFS gaps emitted short lemma names (`add_re`, `apply_symm_apply`,
  `_root_.dvd_iff_mod_eq_zero`) that do not resolve under `import Mathlib`; these were
  rewritten to the global name (`Complex.add_re`, `Equiv.apply_symm_apply`,
  `Nat.dvd_iff_mod_eq_zero`).
- PutnamBench proofs are audited against the official statements; each is also solved
  by ≥1 system on the official leaderboard.

[dspplus]: https://github.com/microsoft/DSP-Plus
[leansatp]: https://github.com/ChristianZ97/LeanSATP/tree/legacy
[q35]: https://huggingface.co/Qwen/Qwen3.5-27B-FP8
[q36]: https://huggingface.co/Qwen/Qwen3.6-27B-FP8
