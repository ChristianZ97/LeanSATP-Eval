# Annotated examples

Two kinds of exhibit; all bodies are verbatim from the verified proofs, with only
inert `--` comments added. Verify in the environment from [`../README.md`](../README.md).

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

## Emit vs. distill (e2e)

`minif2f_mathd_algebra_296.e2e.lean` — an e2e win, where SATP closed the whole theorem
in one `aesop` call. Shows the goal-conditioned config the policy emitted (22 rules,
`maxGoals := 64, enableUnfold := false`, led by abs/integer lemmas) next to the single
`simp_all only [...]` line that aesop's `Try this:` distils it to.
