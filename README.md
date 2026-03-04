# Learnability

Imagine you're reverse-engineering a C program that parses JSON. The program's internal state has hundreds of variables, but the JSON grammar only cares about a few — "am I inside a string?", "what's the current nesting depth?" This framework automatically discovers which variables matter by finding pairs of program states that look the same to your current model but behave differently. Each time it finds such a pair, it adds the distinguishing variable to the model. When it can't find any more such pairs, your model is faithful.

This is a Lean 4 formalization of that idea: extracting faithful behavioral models from observable systems via iterative dimension refinement. The central theorem (`extraction_exists` in `Learnability.lean`) proves that any system with finite behavioral structure, identifiable observations, and a sound oracle admits faithful extraction. 0 sorries.

## Reading order

The same idea is formalized twice — once concretely for labeled transition systems (files 1-3), once abstractly for any observable system (files 4-5).

**Concrete (LTS) chain:** `LTS.lean` → `ConditionalSimulation.lean` → `Convergence.lean`

- `LTS.lean` — labeled transition systems, simulation, traces. Start here for the vocabulary.
- `ConditionalSimulation.lean` — projections, oracle conditions (soundness/realizability/uniformity), simulation theorems. The Galois connection between concrete and projected step relations.
- `Convergence.lean` — iterative dimension refinement converges to a fixpoint where the oracle is sound and non-controllable transitions are invisible. The carving metaphor: each iteration splits an equivalence class that the current projection conflates.

**General framework:** `Learnability.lean` → `CoinductiveBisimulation.lean`

- `Learnability.lean` — the general framework, independent of the LTS chain (imports only Mathlib). Works for any `behavior : State → Label → State → Prop` — not just transition systems but typing judgments, parse relations, effect propagation. Contains the main theorem and all refinement machinery.
- `CoinductiveBisimulation.lean` — capstone: upgrades simulation to bisimulation when the oracle is complete. Both Milner (union-of-bisimulations) and coinductive encodings, with equivalence proof.

## Building

Requires Lean 4 + Mathlib.

```
lake build
```
