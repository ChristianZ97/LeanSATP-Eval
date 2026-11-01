# Thesis Chapter 2 in Lean 4, Draft–Sketch–Prove version

This folder adds a second Lean 4 proof of the results of Section 2.2 of the thesis
("Reward Sparsity Induces an Optimization Plateau"), built in the Draft–Sketch–Prove (DSP) style:

- **Draft.** The draft is the thesis's own informal proof.
- **Sketch.** Every step of that proof becomes one `have` in a Lean sketch, with the proof left as
  a gap.
- **Prove.** The gaps are closed by `satp`, by the generative rule of thesis Section 5.5, by
  `bfsaesop`, and, as a fallback, by Claude Opus 5.5.

The proofs in `../project` (see `../README.md`) were written first and decomposed afterwards. Here
the decomposition comes first, and it follows the thesis text.

The DSP theorems live in `namespace Sec2.DSP`. Their statements are the statements of
`../project`: for each of them, `type_of% @Sec2.DSP.X = type_of% @Sec2.X` holds by `rfl`.

## Layout

```
../project/Sec2/DSP/*.lean, ../project/Sec2/DSP.lean   the DSP proofs (five modules)
../proofs/Sec2DSPAll.lean                             the same, in one file with ../proofs/Sec2All.lean
draft/steps.md                                        the draft: the thesis proofs split into numbered steps
sketch/Sec2/DSP/*.lean                                the sketch, with its 62 gaps
briefs/                                               the instructions given to the sketcher, the generator and Opus
STEPS.md                                              every step and gap, and the stage that closed it
```

## Verify

```bash
cd thesis_ch2/project
lake exe cache get
lake build Sec2 Sec2.DSP
```

## Scope

**In scope: 17 theorems.** Of the 32 public theorems of `../project`, these 17 are asserted or
proved in Section 2.2 of the thesis:

| Thesis | Theorems |
|---|---|
| Setup | `expectedReward_eq`, `gradient_expectedReward`, `norm_gradient_comp_le` |
| Lemma 2.3 | `norm_gradient_expectedReward_le` |
| Proof sketch, θ version | `norm_gradient_expectedReward_comp_le` |
| Lemma 2.4 | `growth` |
| Proposition 2.5 | `optReward_eq`, `plateau` |
| Remark 2.6 | `policy_of_uniform`, `provingProb_of_uniform`, `plateau_uniform`, `provingProb_zero_single`, `uniformSearch_bounds` |
| Lemma 2.7 | `minSamples_sub_isBigO`, `minSamples_isTheta` |
| Corollary 2.8 | `perContext_minTotal`, `perContext_bounds` |

**Cited, not re-proved: 13 theorems.** The thesis gives no proof for these, so there is no draft
to follow. They are basic properties, differentiability, `minSamples_spec`, `minSamples_bounds`,
and the bound on the second derivative that the thesis calls "the bounded Hessian of the softmax"
(`provingProb_deriv2_bound`). The DSP proofs cite them from `../project`, and they cite no other
theorem of `../project`.

## Pipeline

### 1. Draft (`draft/steps.md`)

The proofs of the 17 theorems are split into 61 steps. A step is one of:

- an asserted formula or sentence;
- one link of a displayed chain;
- a formula given as a justification, such as `|1(·) − π^(h)(m|C)| ≤ 1`.

A named principle without a formula, such as "the triangle inequality" or "Taylor expansion",
justifies its step and is not a step itself. Four more items describe the model and are built into
the Lean statements; an example is "all N samples fail with probability (1 − p_s)^N".

### 2. Sketch (`sketch/`, `briefs/SKETCH_BRIEF.md`)

**Who wrote it.** Five Claude Opus 5.5 subagents wrote the sketch, one per module.

- They had no tools. Their only input was the thesis chapter, `draft/steps.md`, and the statements
  of `../project` with every proof replaced by `sorry`.
- They never saw the proofs in `../project`. Their transcripts were audited: every call they made
  was the one that returns their answer.

**The rules.**

- **One step, one gap.** Every step becomes one `have`, one `calc` link or one `obtain`, closed by
  a gap `prove_with [h₁, …]` that lists the hypotheses the step uses.
  - This is the gap syntax of DSP+, which the thesis's DSP evaluation also uses.
  - Before a prover runs, the gap becomes `clear * - h₁ …`, so the prover sees only the listed
    hypotheses.
  - A comment above each gap quotes the thesis step.
- **Citations.** A step that the thesis closes by citing one of its own results ("By Lemma 2.4")
  applies the corresponding theorem and leaves no gap.
- **aux gaps.** A fact that Lean needs and the thesis uses silently becomes a separate gap, marked
  `aux`.
- **Allowed tactics.** Only structural tactics (`intro`, `obtain`, `calc`, `set`, …). The
  sketchers ran no prover.

**Result: 62 gaps.**

- 55 gaps come from thesis steps. Of the other six steps, four are closed by citations.
- The remaining two steps, the lines with `‖∇²_l p_s(ξ)‖₂` and `xᵀ Q x ≤ ‖Q‖₂ ‖x‖₂²`, are merged
  into the next step. The Lean statements have no Hessian object, because
  `provingProb_deriv2_bound` bounds the second derivative along a line.
- 6 gaps are aux.
- 1 gap closes a theorem whose last thesis step is not literally the Lean statement.

**Second pass.** A second pass of the same sketchers added citations of already-proved public
theorems to the context of 11 gaps. Examples are `policy_pos` (π(A|C) > 0) and
`provingProb_nonneg` (p_s ≥ 0).

- `satp` retrieves lemmas only from Mathlib, so it cannot find these theorems by name.
- The steps, the gaps and their statements did not change. Removing the added citations and the
  names they add to the hints, and moving one existing citation back to its place, gives the first
  sketch back, character for character.

To compile the sketch, put `sketch/Sec2/DSP/` in place of `../project/Sec2/DSP/` in a copy of
`../project`. Each gap then elaborates to `clear * - h₁ …; sorry`.

### 3. Prove

Each gap went through four stages in order, and is credited to the first stage that closed it. Each
stage ran on every gap separately, in a file where all the other gaps were `sorry`.

1. **`satp`.** The gap is written `first | ((clear * - h₁ …; satp?); done) | sorry`, as in the
   thesis's DSP evaluation.
   - Each `satp?` call gets 200000 heartbeats, and each file gets 2400 seconds.
   - The policy checkpoint is the one in `../PINS.txt`.
2. **Generative rule** (thesis Section 5.5), for each gap that `satp` leaves.
   - A fresh Opus 5.5 subagent without tools proposed terms t_C for the lemma rules that the search
     of configuration A had run and failed.
   - The orchestrator checked each candidate against the grammar of Section 5.5, built A′, and
     verified it in place.
   - The limits, the early-stop rule and the two author rulings are those used for `../project`
     (see `../README.md` and `../PINS.txt`). The generator ran before `bfsaesop` and got no
     `bfsaesop` hints.
3. **`bfsaesop`**, one attempt per gap, as in the thesis's `satp`→`bfsaesop` cascade.
4. **Claude Opus 5.5**, for the gaps that remain.
   - A fresh subagent without tools saw the gap's goal, its thesis step and the statements of
     `../project`.
   - The orchestrator compiled each submission and returned Lean's messages.
   - The subagent could not cite the theorem it was proving or any later one.
   - After assembly, the subagents whose proofs had linter warnings removed the flagged code in one
     more round (see Lint warnings).

### 4. Assembly

The assembly follows the thesis's released proofs: each `prove_with [h₁, …]` becomes
`clear * - h₁ …` followed by the proof, and each file sets `maxHeartbeats 0`. The `satp` and
`bfsaesop` proofs are their "Try this" outputs, copied verbatim. A comment before each proof names
the stage that produced it. For `satp`, it also quotes the `aesop?` output with configuration A.

## Results

| | Gaps | `satp` | Generative rule | `bfsaesop` | Opus 5.5 |
|---|---|---|---|---|---|
| Thesis steps | 55 | 14 | 0 | 15 | 26 |
| aux | 6 | 2 | 0 | 1 | 3 |
| Conclusion | 1 | 1 | 0 | 0 | 0 |
| **Total** | **62** | **17** | **0** | **16** | **29** |

`STEPS.md` lists every step and gap.

- **`satp` alone, on each whole theorem:** 0 of 17.
- **`satp` on the first sketch**, before the second pass added citations: 16 of 62. The gap it adds
  in the second pass is the last link of Lemma 2.3, with p_s ≥ 0 in context.
- **Whole-file rule.** Under the thesis's rule that a file that times out scores nothing, `satp`
  closes 15 of 62. The two `satp` gaps of Lemma 2.4 sit in a file where another gap times out.
- **`satp` closes mostly short algebraic steps.** Examples from Proposition 2.5 are the equalities in
  the chain `1/p_k − 1/p_{k+1} = …` and the computation `J* − J(l_k) = Δ_r(1 − p_k) ≥ Δ_r(1 − 2p_0)`.
- **The generative rule closes none of the 45 gaps that `satp` leaves.**
  - 10 gaps have no editable lemma rule.
  - On 34 of the other 35, the generator stopped after one round, with an argument that no
    arguments can work: the editable lemma rules do not mention the objects these steps need
    (softmax, gradients, the ascent iteration, filters).
  - On the last one, it used up its budget (3 rounds).
  - On the smaller, Mathlib-only leaves of `../project`, the generative rule closed 5 of 64.
- **Gap 18.** `bfsaesop` found a proof, but its "Try this" output does not replay
  (`No goals to be solved`). The gap is credited to Opus 5.5.

## Verification

1. `lake build Sec2 Sec2.DSP` reports no errors.
2. No `sorry`, `admit`, `native_decide`, `axiom` or `unsafe` declaration appears. The only option
   is `set_option maxHeartbeats 0` in each file header.
3. `#print axioms` on each of the 17 theorems gives `propext`, `Classical.choice` and `Quot.sound`
   only.
4. For each of the 17 theorems, `type_of% @Sec2.DSP.X = type_of% @Sec2.X` holds by `rfl`.
5. **Dependencies.**
   - No proof uses one of the 17 in-scope theorems of `../project`.
   - None does so indirectly either, through the cited theorems.
   - A positive control found the expected dependencies of `Sec2.plateau`.
6. **The sketch is unchanged.** Replacing each proof by its `prove_with` gives the sketch back,
   character for character.
7. `../proofs/Sec2DSPAll.lean` compiles with `lake env lean` in the LeanSATP v4.27 workspace.

## Lint warnings

`lake build Sec2 Sec2.DSP` reports 18 linter warnings and no errors:

- 12 are in `../project`, the same as before.
- 6 are in copied `bfsaesop` "Try this" proofs, kept verbatim: 2 unused simp arguments, 3 places
  where `<;>` could be `;`, and 1 suggestion to merge `intro`s.

The Opus 5.5 proofs at first had 212 warnings, almost all for `first | … | …` alternatives that
never ran. After assembly, each of the 16 subagents whose proof had warnings was asked, in the same
conversation, to remove what the linter flagged (`briefs/OPUS_BRIEF.md`).

- The revisions only delete code. The one exception is a deprecated name, replaced as Lean
  suggested.
- The revisions passed the same checks as before.

## Differences from the thesis's DSP evaluation

- **One sketch.** There is one sketch, of the thesis's own proof. The thesis evaluation instead
  samples 32 sketches from an LLM drafter and sketcher.
- **No e2e first try.** The pipeline has no end-to-end first try; it is reported above as a
  baseline instead.
- **Generative-rule stage.** A generative-rule stage sits between `satp` and `bfsaesop`.
- **Per-gap credit.** Each gap is credited separately.
- **Opens.** Each file keeps its module's own `open` line rather than the miniF2F header, so that
  the names in the copied outputs resolve as they did in the search.

## Model use

Claude Opus 5.5 subagents, input and output tokens:

| Stage | Input tokens | Output tokens |
|---|---|---|
| Sketch, both passes | 2.4M | 0.85M |
| Generator | 6.8M | 1.7M |
| Fallback prover, with the cleanup round | 4.1M | 1.9M |

The orchestrating session is not included. `bfsaesop` ran BFS-Prover-V2-7B on local GPUs.
