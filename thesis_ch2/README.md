# Thesis Chapter 2 in Lean 4

A complete Lean 4 + Mathlib formalization of Chapter 2, *Formulating Solver Configuration*, of the SATP master's thesis (Section 2 of the journal version). It covers the Setup remark and Lemma 2.3 through Corollary 2.8.

- **Faithful:** the Lean statements say what the thesis says, under the thesis's own setup and assumptions; `O(·)`, `Θ(·)` and "sufficiently small" become explicit constants (see `STATEMENTS.md`).
- **Zero `sorry`:** every result is proved.
- **Axioms:** every public declaration depends only on `propext`, `Classical.choice` and `Quot.sound`.
- **Proof structure:** the proofs are broken down into 137 single-step *leaf* lemmas. Wherever possible, a leaf is closed by the configuration that `satp` emits, copied verbatim, and a comment records how the step was proved.
- **DSP version:** `dsp/` holds a second proof of the results of Section 2.2. It follows the thesis text step by step (Draft–Sketch–Prove); see [`dsp/README.md`](dsp/README.md).

## Layout

```
project/                   Lake project on stock Mathlib (Lean v4.27.0, Mathlib a3a10db0e9)
  Sec2/Basic.lean            Setup: softmax policy (2.1), proving probability p_s, J_sparse, gradients, chain rule
  Sec2/SelfBound.lean        Lemma 2.3 (Self-bounding gradient)
  Sec2/Growth.lean           Lemma 2.4 (Quadratic per-step growth), with the second-derivative bound it relies on
  Sec2/Plateau.lean          Proposition 2.5 (Sparsity inflates verification cost), Remark 2.6 (Implication)
  Sec2/RandomSearch.lean     Lemma 2.7 (Random search costs Θ(1/p_s)), Corollary 2.8 (Cost of per-context search)
  Sec2/DSP/*.lean            the DSP version of the Section 2.2 proofs (namespace Sec2.DSP; see dsp/)
proofs/Sec2All.lean        the five modules in one file, checked with `lake env lean` like the rest of this repository
proofs/Sec2DSPAll.lean     the five modules and the DSP modules in one file
dsp/                       the DSP version: draft, sketch, briefs, README and STEPS
STATEMENTS.md              thesis-to-Lean mapping of every statement, with the modeling choices
LEAVES.md                  all 137 leaves and how each one is proved
PINS.txt                   versions, checkpoints and the verification gate
```

## Verify

Stock Mathlib:

```bash
cd thesis_ch2/project
lake exe cache get
lake build
```

LeanSATP v4.27 workspace, after `./setup.sh`, from the LeanSATP repository root:

```bash
lake env lean <path-to>/thesis_ch2/proofs/Sec2All.lean
```

Neither path needs LeanSATP or a running service: the `satp` and `bfsaesop` outputs below are plain Lean.

## How each leaf is proved

Each public theorem's proof only assembles leaves. Every reasoning step (an identity, an inequality, a positivity fact, a derivative formula, a manipulation of a finite sum) is a separate private lemma whose statement uses only Mathlib notions. The comment at the top of each leaf proof carries one of four tags.

| Tag | Meaning | Proof body |
|---|---|---|
| `[satp policy infer]` | satp's policy infers configuration A, and `aesop` proves the leaf with A | the `satp?` "Try this" output, copied verbatim; the `aesop?` "Try this" output with A (the proof `aesop` found) is copied in a comment |
| `[satp + generative rule]` | A fails; a generator g supplies a term t_C as the arguments of one lemma rule of A, giving A′ | the full A′; a comment shows the one rule in which A and A′ differ, plus the `aesop?` output with A′ |
| `[bfsaesop]` | A fails and no generative rule is found; `bfsaesop` (aesop guided by BFS-Prover-V2) proves the leaf | the `bfsaesop` "Try this" output, copied verbatim |
| `[non-satp]` | all of the above fail | a proof written by Claude Opus 5.5 subagents |

A generative-rule leaf, for example:

```lean
private lemma exp_neg_pow_eq (p : ℝ) (N : ℕ) :
    Real.exp (-p) ^ N = Real.exp (-(p * N)) := by
  -- [satp + generative rule] ...
  --   A : (add norm 0 (by grind only [Real.exp_nat_mul]))
  --   A′: (add norm 0 (by grind only [Real.exp_nat_mul (-p) N, Real.exp_nat_mul p N]))
  aesop (config := { ... })
      ...
  -- The `aesop?` "Try this" output with A′ ...:
  --   (ring_nf)
  --   (grind only [Real.exp_nat_mul (-p) N, Real.exp_nat_mul p N])
```

## Results

| Module | Leaves | satp policy infer | satp + generative rule | bfsaesop | non-satp |
|---|---|---|---|---|---|
| `Basic` | 14 | 2 | 1 | 8 | 3 |
| `SelfBound` | 21 | 9 | 0 | 7 | 5 |
| `Growth` | 48 | 26 | 2 | 13 | 7 |
| `Plateau` | 31 | 22 | 1 | 4 | 4 |
| `RandomSearch` | 23 | 14 | 1 | 5 | 3 |
| **Total** | **137** | **73** | **5** | **37** | **22** |

satp proves 78 of the 137 leaves: 73 with the configuration its policy infers, and 5 more with one generative rule.

**The five generative rules.** In each case, arguments drawn only from names in the context do not prove the leaf, so the constructed term is necessary. Two of the five leaves are also out of reach for `bfsaesop`.

| Leaf | Rule in A → rule in A′ |
|---|---|
| `Basic.sum_div_sum_eq_one` | `grind only [Finset.mul_sum]` → `grind only [Finset.mul_sum Finset.univ x (Inv.inv (∑ ι, x ι))]` |
| `Growth.sum_div_sum_self_eq_one` | `grind only [Finset.mul_sum]` → `grind only [Finset.mul_sum Finset.univ E (Inv.inv (∑ m, E m))]` |
| `Growth.mul_sum_four_mul_eq` | `grind only [Finset.sum_mul]` → `grind only [Finset.sum_mul univ D 4]` |
| `Plateau.one_div_two_mul_le_sub` | `grind only [div_eq_inv_mul]` → `grind only [div_eq_inv_mul 2 (2 * p0)]` |
| `RandomSearch.exp_neg_pow_eq` | `grind only [Real.exp_nat_mul]` → `grind only [Real.exp_nat_mul (-p) N, Real.exp_nat_mul p N]` |

`Growth.sum_div_sum_self_eq_one` and `RandomSearch.exp_neg_pow_eq` are the two that `bfsaesop` cannot prove.

**Generative-rule protocol (thesis Section 5.5).** The rules are the same as in the thesis:

- A′ differs from A by one rule. t_C supplies only the arguments of a lemma rule that the search of A runs and that fails, and the rule type, priority, position, wrapper and lemma stay the same.
- t_C contains no tactics and no lemmas other than projections of hypotheses.
- The heartbeat budget is the same as for satp.
- The generator g is an Opus 5.5 subagent.

Two clarifications were fixed by the author:

1. A term that only selects names from the context is not counted as a construction.
2. t_C may not build functions from combinators such as `Function.swap` or `Function.comp`.

Under these rulings, two further A′ that the search found are not counted, and those leaves are tagged by their next method.

## Formalization choices

`STATEMENTS.md` maps each thesis statement to its Lean statement. The statements follow the thesis; these choices make it precise:

- Lemma 2.7 starts, as the thesis's proof does, from the probability `(1 − p_s)^N` that `N` independent samples all fail; product measures are not formalized.
- The Setup's simplification `M_h = M` is the thesis's own.
- The "sufficiently small step size" of Lemma 2.4 is made explicit: `0 < α ≤ 1/((4H + 1) Δ_r)` with `c = 2 α H M Δ_r`.
- The thesis's proof of Lemma 2.4 uses a bound on the second derivative of the softmax policy without proving it. That bound is proved here (`provingProb_deriv2_bound`).

## Linter warnings

`lake build` reports 12 linter warnings and no errors. None is in the glue:

- 9 come from the copied `bfsaesop` proofs: unused simp arguments, unreachable `ring`, and an unnecessary `<;>`.
- 1 is an unused hypothesis of a satp leaf.
- 2 are unused hypotheses that the public statements keep for fidelity to the thesis.

The copied text is kept verbatim on purpose.
