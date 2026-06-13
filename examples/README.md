# Annotated examples

All bodies are verbatim from the verified proofs; the only additions are inert `--`
comments. Verify in the environment from [`../README.md`](../README.md).

## Gap-tagged cascade proofs

Each `have` is one sketch gap, tagged by the solver that closed it: `[satp]` (the 0.2B
SATP policy — one `aesop` config, full ruleset in `proofs_aesop_config/`) or `[bfs]`
(BFS-Prover-V2-7B).

| file | problem | gaps (satp / bfs) |
|---|---|---|
| `minif2f_mathd_algebra_362.annotated.lean` | `mathd_algebra_362` (MiniF2F-test) | 4 / 4 |
| `putnam_1986_a1.annotated.lean` | `putnam_1986_a1` (PutnamBench) | 11 / 3 |

- `mathd_algebra_362` — SATP closes the rearrange/substitute/evaluate gaps; BFS the
  two cube-root extractions (case-split + `nlinarith`).
- `putnam_1986_a1` — SATP closes the 11 routine gaps (unfold `f`, `deriv f`, evaluate
  `f` at the endpoints); BFS the 3 hard ones: `S = [-3,-2] ∪ [2,3]`, the bound
  `∀ x ∈ S, f x ≤ 18`, and `IsGreatest`.

## e2e emit (config necessary vs default aesop)

`minif2f_mathd_algebra_302.e2e.lean` — an e2e win, where satp closed the whole theorem
in one `aesop` call. Vanilla `aesop` (no added config) does **not** close `(i/2)² = −1/4`;
the emitted config does. The config is goal-conditioned (`maxNormIterations := 160`,
`maxGoals := 64`, Complex lemmas), and aesop's `Try this:` reduces it to a short
Complex-arithmetic proof (`Complex.I_sq` + `ring`).
