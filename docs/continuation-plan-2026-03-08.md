# Continuation Plan 2026-03-08

## Current theorem stack

Committed and built:

- `bc1e2dfb` `add generic observation-level model equivalence`
- `97a6f251` `add VEX observation-level model equivalence bridge`
- `f1dfdc65` `add VEX ModelEq corollaries`
- `764aff04` `add fixed-path VEX extractibility theorem`
- `619ed760` `add VEX path append and executable composition lemmas`
- `ab9bbab7` `add VEX path composition model equivalence theorem`
- `8e049bd7` `add fetched-block VEX program-step extractibility theorem`
- `be12fdc0` `add fetched-block VEX program-trace extractibility theorem`
- `4240bd8a` `add VEX path-family subsystem extractibility theorem`
- `0bde9acc` `add extensional VEX witness completeness layer`
- `09f9746f` `add extensional VEX loop region wrapper`
- `b5b9ad7f` `add bounded VEX loop witness object`
- `3cfde8ca` `add VEX loop witness completeness wrapper`

Working copy is clean after `3cfde8ca`.

## What these mean

### Model equivalence layer

Generic:
- `ModelDenotesObs`
- `SummaryEq`
- `ModelEq`
- `ModelEqState`

VEX instantiation:
- `VexModelDenotesObs`
- `VexModelEq`
- block/path adequacy theorems

This is the repaired convergence object direction: semantic equality up to relevant observed behavior, not raw syntax equality.

### Extractibility layer

Done:
1. `ExtractiblePathModel`
2. `ExtractiblePathModel.compose`
3. `ExtractibleProgramStep`
4. `ExtractibleProgramTrace`
5. `ExtractiblePathFamilyModel`

These now cover:
- fixed lifted paths
- composition of paths
- fetched one-step program semantics
- fetched finite traces
- finite path-family subsystem witnesses

### Witness-first convergence layer

Done:
- `Region`
- `WitnessComplete`
- `extractedModel_of_witnessComplete`
- `completeWitnesses_modelEq`
- `LoopRegionSpec`
- `LoopRegion`
- `repeatBlockPath`
- `boundedLoopWitness`
- `LoopWitnessComplete`
- `extractedLoopModel_of_witnessComplete`

This is the key split:
- witness semantics: what a complete witness buys you
- witness existence: still open

## Root decision already made

Proceed witness-first, not region-first.

Meaning:
- the real open problem is witness existence / witness completeness for loops
- convergence should be restated as existence of a finite complete witness
- not as a separate abstract syntax-level stabilization story

## Most likely next theorem boundary

Do **not** jump straight to circular coinduction proof glue.

Next step should be to define the exact hypothesis that would imply
`LoopWitnessComplete spec body K`.

Likely shape:

```lean
def LoopUnrollBound
    (spec : LoopRegionSpec Reg Obs)
    (body : List (Block Reg))
    (K : Nat) : Prop :=
  forall s o,
    spec.DenotesObs s o ->
      ExecPathFamilyDenotesObs spec.Relevant spec.observe
        (boundedLoopWitness body K) s o
```

Then probably a second direction/soundness hypothesis if needed, depending on how loop-region `DenotesObs` is fixed.

Likely theorem target:

```lean
theorem loopWitnessComplete_of_unrollBound
    ... :
    LoopWitnessComplete spec body K
```

That theorem is the plug point for:
- circular coinduction / stabilization
- finite-state recurrence / bounded orbit arguments

## Why this is the next step

The packaging work is done.
The next open question is no longer “what is the object?”
It is “what exact bound hypothesis makes the witness complete?”

That is the first place where the old loop convergence machinery can be honestly reattached.

## Notes on what not to do next

Do not:
- add decorative CFG/entry/exit machinery yet
- add `SubsystemWitness` packaging yet
- return to raw-syntax stabilization claims
- over-generalize region structure before the witness-existence theorem shape is pinned down

## If continuing fresh

Recommended next sequence:
1. define the loop-bound hypothesis object precisely
2. prove the small theorem from that hypothesis to `LoopWitnessComplete`
3. only then connect stabilization / finite-state results to that hypothesis

If theorem-shape review is desired before coding, review the exact `LoopUnrollBound` / `loopWitnessComplete_of_unrollBound` interface first.
