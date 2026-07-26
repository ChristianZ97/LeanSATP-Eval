# LeanSATP-Eval (v2)

Lean 4 proofs from a DSP+ pipeline; subgoals closed by an SATP→BFS cascade.
All proofs compile with `lake env lean` on stock Mathlib, no prover server.

This branch uses the **v2 SATP checkpoint** (factored joint-action heads) in a
Lean `v4.26.0` environment. See [main][main] for the v1 (paper) release.

| Benchmark | Proved |
|---|---|
| MiniF2F-Test | 78.7% (192 / 244) |

`#print axioms` on each proof: `[propext, Classical.choice, Quot.sound]`, no
`sorryAx` — except `amc12a_2020_p4` (see Notes).

## Pipeline

[DSP+][dspplus] three stages:

1. Draft — an LLM writes an informal proof.
2. Sketch — the same LLM formalizes it into Lean 4 with a `sorry` per subgoal.
3. Prove — each `sorry` is closed by the `satpbfsaesop4x` cascade: the 0.2B
   [LeanSATP][leansatp] v2 policy emits one `aesop` config; gaps it misses go to
   BFS-Prover-V2-7B, up to ×4.

Drafter & Sketcher: [Qwen3.5-27B-FP8][q35], reused from the v1 generation — only
the SATP checkpoint and the Lean environment changed between the two branches.

## Layout

```
minif2f/proofs/<p>.lean               minimized tactics
minif2f/proofs_aesop_config/<p>.lean  same proof, SATP's emitted aesop config
```

`proofs/` is the minimized form (aesop `Try this:`). `proofs_aesop_config/` keeps
the `aesop (config := …) (add …)` block SATP emitted, e.g.
`minif2f/proofs_aesop_config/amc12a_2021_p18.lean`.

## Verify

Built and checked in the [LeanSATP][leansatp] v2 environment:

```bash
git clone --branch v2 https://github.com/ChristianZ97/LeanSATP
lake env lean /path/to/minif2f/proofs/amc12a_2002_p6.lean
```

Environment: lean4 `v4.26.0`, Mathlib `2df2f0150c`, stock aesop. The environment
changes no `Mathlib/*.lean` files; the proofs use no fork-only aesop options.

## Notes

- Short lemma names some BFS gaps emitted (`add_re`, `apply_symm_apply`,
  `_root_.dvd_iff_mod_eq_zero`) were rewritten to the global name
  (`Complex.add_re`, `Equiv.apply_symm_apply`, `Nat.dvd_iff_mod_eq_zero`) so they
  resolve under `import Mathlib`.
- 31 of the 244 test statements use the pre-v4.26 `∑ x in s, f` big-operator
  syntax. A one-line notation shim in each proof header (`_BIGOP_COMPAT`) restores
  it without editing the statement.
- `amc12a_2020_p4` closes its counting subgoal with `native_decide` (a
  9000-element digit-filter cardinality check, infeasible for kernel `decide`), so
  it depends on `Lean.ofReduceBool` / `Lean.trustCompiler` beyond the standard
  trio; a header comment in that file flags it.

## Provenance

These files were re-derived by re-running each solved problem's `satpbfsaesop4x`
cascade in the LeanSATP v2 environment, capturing the emitted `aesop` config
(and, for BFS-closed gaps, the minimal `Try this:` tactics), then verifying each
standalone (`lake env lean`, rc 0, `#print axioms` as above). The SATP branch is
deterministic; BFS branches are sampled, so a re-derivation reproduces *a* valid
closure of each gap, not necessarily the original bank draw.

For the per-mode pass rates and reproducibility bands see the
[LeanSATP v2 README][leansatp] and the [satp-policy-v2 model card][card].
PutnamBench under the v2 checkpoint is a separate run (in progress) and is not
part of this branch yet.

[dspplus]: https://github.com/microsoft/DSP-Plus
[leansatp]: https://github.com/ChristianZ97/LeanSATP/tree/v2
[main]: https://github.com/ChristianZ97/LeanSATP-Eval/tree/main
[q35]: https://huggingface.co/Qwen/Qwen3.5-27B-FP8
[card]: https://huggingface.co/ChristianZ97/satp-policy-v2
