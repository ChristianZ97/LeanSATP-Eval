import Mathlib.Tactic.ClearExcept

/-!
# The gap tactic `prove_with` (DSP+ convention)

A sketch closes each step with a gap `prove_with [h₁, …, hₙ]` that lists the local hypotheses
the step uses. The gap expands to

    (clear * - h₁ … hₙ; sorry)

It clears every other hypothesis, then closes the goal with `sorry`. Mathlib's `clear * -`
keeps type-class instances, and it cannot clear what the goal or a listed hypothesis depends on,
so the variables the goal mentions stay. A name that is not a local hypothesis is an error.
`prove_with []` and a bare `prove_with` expand to `(clear * -; sorry)` and keep no hypotheses.

This is the same rewrite that the paper's pipeline applies to a gap before a prover runs
(`_clear_fragment` in its `build_stages.py`): the comma-separated hints become
`clear * - h₁ … hₙ`, an empty list becomes `clear * -`, and the prover's tactic takes the
place of `sorry`.
-/

syntax (name := proveWith) "prove_with" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| prove_with [$hs,*]) => `(tactic| (clear * - $(hs.getElems)*; sorry))
  | `(tactic| prove_with) => `(tactic| (clear * -; sorry))
