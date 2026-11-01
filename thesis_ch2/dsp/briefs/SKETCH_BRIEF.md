# Brief for the sketcher (DSP run, thesis Chapter 2)

You turn the thesis's informal proofs into Lean 4 **sketches**, in the style of DSP+.

- A sketch is a proof whose every reasoning step is an explicit `have` closed by a gap,
  `prove_with [h₁, …]`.
- You do not prove the steps. Automated provers fill the gaps later.

## How this works

- **No tools.** You have no tools and need none. Do not try to read files or run commands.
- **Inputs.** Everything you need is in this prompt, after this brief:
  1. `steps.md`: the thesis's proofs split into numbered steps, with the scope and the
     formalization notes for each theorem.
  2. Section 2.2 of the thesis, in LaTeX. Line numbers in `steps.md` refer to it.
  3. The statement skeleton, `Sec2/*.lean` (5 modules). It holds the definitions and the 32
     public theorem statements with their docstrings; the 30 proofs are `sorry`.
  4. `Sec2/DSP/ProveWith.lean`, which defines the gap tactic `prove_with`.
  5. Your assignment: one module (`Basic`, `SelfBound`, `Growth`, `Plateau` or `RandomSearch`).
- **Reply.** Send one fenced `lean` block holding the whole file `Sec2/DSP/<Module>.lean`. After
  it, send your report (see the end of this brief).
- **Compile errors.** The orchestrator compiles your file and sends back Lean's errors. Fix them
  and resend the whole file and the updated report. Fix only what the errors require; do not
  restructure steps in response to an error unless the error shows the step is mis-stated.

## The file

- `import Sec2.<Module>` (the matching skeleton module) and `import Sec2.DSP.ProveWith`, nothing
  else.
  - Other DSP modules are sketched in parallel; the orchestrator adds the imports between DSP
    modules afterwards.
- The skeleton module's `open` line.
- `variable {H M : ℕ}` where the skeleton module declares it.
- `namespace Sec2.DSP` … `end Sec2.DSP`.

For each theorem of your module that `steps.md` lists:

- restate it in `namespace Sec2.DSP` under the same name;
- copy its docstring and its statement character for character from the skeleton;
- replace the proof by the sketch.

Theorems keep the order of `steps.md`.

**Names.** Inside `Sec2.DSP`, a bare name resolves to the `Sec2.DSP` version when there is one,
and to the `Sec2` version otherwise.

- Citing `growth` in `plateau` cites the skeleton's `growth` while you sketch, and the DSP
  `growth` once the DSP modules import each other. The statements are identical, so the cite
  typechecks either way.
- Write cites as bare names, never `Sec2.growth` or `Sec2.DSP.growth`.
- Never cite the theorem you are proving.

## What a sketch may contain

**Every thesis step of `steps.md` (except those labelled model) becomes exactly one of:**

- `have <name> : <statement> := by prove_with [h₁, …]`
- one link of a `calc` chain: `_ ≤ <term> := by prove_with [h₁, …]`
- `obtain ⟨…⟩ : <∃-statement> := by prove_with [h₁, …]`, when the step introduces an object,
  as in "for some ξ"

**One step, one gap.**

- Do not merge two thesis steps into one gap, and do not split one step into several.
- If a step needs several Lean facts, keep it as one `have`, and let the gap carry the work.
- The only merges allowed are those `steps.md` describes (for example in Lemma 2.4). Record each
  one in the comment.

**Comment.** Directly above each gap, write a comment with the step ID and the thesis text in
Unicode:

```lean
-- [L23.7] ≤ Σ_{A∈𝒜*} π(A|C)   (the triangle inequality and L23.8)
```

**The hint list of `prove_with`.**

- List the local hypotheses the step uses: theorem hypotheses (such as `hr`), and earlier `have`s
  or `obtain`s.
- Follow the thesis's justification. For example, "(the triangle inequality and L23.8)" lists the
  `have` of L23.8.
- A `calc` link's left-hand side comes from the previous link. Do not list it.
- Variables that the goal mentions are kept automatically.
- The provers see only what you list, so an omitted hypothesis can make a true step unprovable.
  When unsure whether a step uses a hypothesis, list it.
- `prove_with []` keeps no hypotheses.

**Cites (no gap).** A step may be closed without a gap only when it is a cite: a term that applies
one of the 32 public theorems of `Sec2`, or an earlier `Sec2.DSP` theorem. For example:

```lean
-- [P25.1, cite: growth]
have h := growth hM Astar rs rf hr α hα hαle (ascent Astar rs rf α l₀ k)
```

- Applying a Mathlib lemma is proof work, even when you know which lemma would do it (for
  example Taylor's theorem). It belongs in a gap.
- A cite term may use `funext`, anonymous constructors and projections (`.1`, `.le`, `⟨_, _⟩`),
  but nothing that searches.

**aux gaps.** Lean sometimes needs a fact that the thesis uses silently. Examples: a positivity
side condition for a division, differentiability for Taylor's theorem, or the equation between two
renderings of the same quantity.

- Add `have <name> : <fact> := by prove_with [...]` with the comment `-- [aux] <one-line reason>`.
- Keep aux gaps few and small.
- Never put a thesis step inside an aux gap.

**The theorem's goal.**

- If the last step is literally the goal, close the goal with `exact <that have>`.
- Otherwise add one gap labelled `-- [conclusion]`.

**Allowed tactics.** These only arrange the proof; they do not search.

- Introducing: `intro`, `rintro`, `obtain` and `rcases` (on hypotheses or on `have`s),
  `constructor`, `refine ⟨?_, ?_⟩`, `refine fun … => ?_`.
- Naming: `set … with …`, `generalize`, `let`.
- Steps: `have`, `calc`, `show` (to restate the goal up to definitional unfolding), `suffices`.
- Unfolding: `unfold` or `delta` of the thesis's definitions (`softmax`, `policy`,
  `provingProb`, `reward`, `expectedReward`, `ascentStep`, `ascent`, `optReward`, `minSamples`).
- Closing: `exact <hypothesis or have>`, `exact <cite term>`, `prove_with [...]`.
- Contradiction: `by_contra`.

Everything else (`simp`, `rw`, `linarith`, `nlinarith`, `field_simp`, `ring`, `norm_num`,
`positivity`, `omega`, `gcongr`, `aesop`, `induction`, `decide`, `apply`, `exact?`, `sorry`, …)
is either proof work or a raw gap. Proof work belongs in a gap. Every gap is written `prove_with`.

**Truth.** Every `have` must be true in its context exactly as you state it. A prover cannot prove
a false step, and a false step is a sketch error. Check the side conditions:

- division by zero and Lean's `x / 0 = 0`;
- natural-number subtraction and casts;
- `Real.log` of nonpositive numbers;
- the direction of an inequality after dividing by a negative number.

If a thesis step needs a side condition to be true, add it as an aux gap before the step, and list
it in the step's `prove_with`. Do not weaken the step.

**Faithfulness.**

- Each `have` states what its thesis step says, in the vocabulary of the skeleton.
- Add no steps of your own reasoning beyond the aux facts above.
- When a step's Lean counterpart cannot be stated (see the merging note for Lemma 2.4 in
  `steps.md`), merge it as described there and record the merge in the comment.

## Before you reply

1. Every step ID of your theorems in `steps.md`, except those labelled model, appears exactly once
   in a comment, as a gap or as a cite.
2. Every `prove_with` has a comment directly above it with a step ID, `[aux]` or `[conclusion]`.
3. The docstring and statement of each theorem are character for character the skeleton's.
4. Every hint list names only hypotheses that exist at that point.

## Report (after the Lean block)

- Per theorem: the steps, and the number of gaps, split into thesis steps, aux and conclusion.
- Every merge, and why.
- Every place where a thesis step needed a side condition or could not be stated as written. For
  example, a step that is false as written, or a step the Lean statement does not need.
- Anything in the thesis text that you found ambiguous, and how you read it.
