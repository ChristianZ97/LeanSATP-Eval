# Annotated proofs

One annotated proof per benchmark, each `have` tagged by the solver that closed it.
Tactic bodies are verbatim from `proofs/`; the only additions are inert `--` comments.
Verify in the environment from [`../README.md`](../README.md).

| file | problem | gaps (satp / bfs) |
|---|---|---|
| `minif2f_mathd_algebra_362.annotated.lean` | `mathd_algebra_362` (MiniF2F-test) | 4 / 4 |
| `putnam_1986_a1.annotated.lean` | `putnam_1986_a1` (PutnamBench) | 11 / 3 |

- `[satp]` — the 0.2B SATP policy (one `aesop` config; the full emitted ruleset is in
  `proofs_aesop_config/`).
- `[bfs]` — BFS-Prover-V2-7B.

Split:

- `mathd_algebra_362` — SATP closes the rearrange/substitute/evaluate gaps; BFS the
  two cube-root extractions (case-split + `nlinarith`).
- `putnam_1986_a1` — SATP closes the 11 routine gaps (unfold `f`, `deriv f`, evaluate
  `f` at the endpoints); BFS the 3 hard ones: `S = [-3,-2] ∪ [2,3]`, the bound
  `∀ x ∈ S, f x ≤ 18`, and `IsGreatest`.
