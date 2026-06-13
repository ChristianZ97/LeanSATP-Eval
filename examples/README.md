# Annotated proofs

One annotated proof per benchmark, taken verbatim from the corpus and re-verified
with `lake env lean`. The only additions are a header block and one `--` comment per
gap; the comments are inert. Verify in the environment from [`../README.md`](../README.md).

| file | problem | gaps | histogram |
|---|---|---|---|
| `minif2f_mathd_algebra_362.annotated.lean` | MiniF2F-test / `mathd_algebra_362` | 8 | `{satp: 4, bfs_1: 4}` |
| `putnam_1986_a1.annotated.lean` | PutnamBench / `putnam_1986_a1` | 14 | `{satp: 11, bfs_1: 3}` |

Each `have` is one sketch gap. The tag records which solver closed it:

- `[satp]` — the 0.2B SATP policy, one `aesop (config := …) (add …)` ruleset (single
  argmax call). The block is shown the first time it appears and is identical for
  every later `[satp]` gap.
- `[BFS-1]` — BFS-Prover-V2-7B, attempt 1.

Per-proof split:

- `mathd_algebra_362` — SATP closes the rearrange/substitute/evaluate gaps
  (h2, h5, h8, h9); BFS closes the two cube-root extractions needing a
  `b = 0 ∨ b ≠ 0` split + `nlinarith` (h3/h4, h6/h7).
- `putnam_1986_a1` — SATP closes 11 gaps (unfold `f`, `deriv f`, evaluate `f` at the
  endpoints, locate critical points); BFS closes 3: characterise `S` as
  `[-3,-2] ∪ [2,3]` (h1), the bound `∀ x ∈ S, f x ≤ 18` (h13), and `IsGreatest` (h14).

These use the `proofs_aesop_config/` variant so the emitted ruleset is visible;
`proofs/` carries the minimized form for the same theorems.
