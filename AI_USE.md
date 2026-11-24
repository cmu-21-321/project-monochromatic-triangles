# AI-Use Statement

## Tools

We used **Claude** and **ChatGPT**

## How we used it

**Planning the proof of Goodman's identity.** We used Claude to brainstorm and go back and forth on how to break `goodman_identity` into smaller lemmas. We discussed counting pairs of a vertex and a triangle in two ways, what each intermediate lemma should state, and the order in which to prove them. The final decomposition (mixed triples, fibres over triangles, and the per-triangle contribution) was settled by us over several iterations.

**Refactoring code.** We used Claude to refactor code in both `ProjectTemplate/Basic.lean` and `ProjectTemplate/MoreLemmas.lean`. This included restructuring definitions after instructor feedback. For example, we replaced an existential inside the monochromaticity predicate with an explicit colour argument (`isMonochromaticWith`) and defined `monoCount` as a sum over colours.

**Learning Lean.** We asked Claude to explain Lean and Mathlib concepts we had not seen before, including decidability instances, `noncomputable`, and tactics such as `zify`, and `interval_cases`.

## Our responsibility
We understand all code in the project and can explain any part of it.
