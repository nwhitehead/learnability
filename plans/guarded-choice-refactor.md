# Plan: guardedChoice Refactor + LoopSummary Complementarity

## Status
- **Branch:** `ictac-computability`
- **Last clean commit:** `f0e740f8` — guardedChoice constructor added to CompTree
- **Working copy:** CLEAN (broken afterBody migration reverted)
- **Build:** 741 jobs, 0 sorries, 0 errors, 0 warnings

## Background

Sophie's insight: "CompTree should always have been guarded." Every actual use
of `choice` in the codebase is already guarded:
- `afterBody`: `choice (assert exits) (seq (assert continues) ...)`
- `guardedLoopTree`: same pattern
- `ite'` (ProgramStructure.lean:278): `choice (seq (assert φ) t₁) (seq (assert (pc_not φ)) t₂)`

The raw `choice` constructor is arbitrary nondeterminism. Nobody constructs
bare unguarded choice. This is a representation problem — the syntax doesn't
enforce what the code already does.

`guardedChoice guard tThen tElse` was added in `f0e740f8`. Its semantics are
definitionally equal to `choice (seq (assert guard) tThen) (seq (assert (pc_not guard)) tElse)`.

## The Blocker (CONFIRMED BY BUILD FAILURE)

Migrating `afterBody` from `choice` to `guardedChoice` changes the proof
obligations. `guardedChoice exits skip (seq (assert continues) ...)` introduces
`assertBehavior (pc_not exits)` structurally on the else branch, PLUS the
explicit `assertBehavior continues` inside.

The backward direction of `afterBody_behavior` needs to produce
`satisfies s (pc_not exits)` but only has `satisfies s continues`. These are
independent PCs in `LoopSummary` — no constraint relates them.

**Sophie's decision:** Add complementarity field to LoopSummary. "obvs 1."

## Commit Sequence

### Commit 1: Add `guard_complement` field to LoopSummary

Add to `LoopSummary` structure:
```lean
guard_complement : ∀ s, isa.satisfies s continues → isa.satisfies s (isa.pc_not exits)
```

The weakest sufficient form: one-directional implication `continues → pc_not exits`.
The strong form (biconditional) is more honest but needs `pc_not` involution properties.
Start with the weak form — can strengthen later.

**Propagation:** Every construction of `LoopSummary` must provide this field.
Need to check how many places construct LoopSummary values.

**Files touched:** CircularCoinduction.lean (structure definition + constructors)

### Commit 2: Migrate `afterBody` to `guardedChoice`

Change:
```lean
| n + 1 => .choice
    (.assert summary.exits)
    (.seq (.assert summary.continues) (.seq summary.body (afterBody summary n)))
```
To:
```lean
| n + 1 => .guardedChoice summary.exits
    .skip
    (.seq (.assert summary.continues) (.seq summary.body (afterBody summary n)))
```

Fix `afterBody_behavior` proof — use `guard_complement` to produce
`satisfies s (pc_not exits)` from `satisfies s continues`.

**Files touched:** CircularCoinduction.lean (~395-400, ~467-520)

### Commit 3: Migrate `guardedLoopTree` to `guardedChoice`

Same pattern. Change:
```lean
| n + 1 => .choice
    (.assert summary.exits)
    (.seq summary.body (afterBody isa summary n))
```
To:
```lean
| n + 1 => .guardedChoice summary.exits
    .skip
    (.seq summary.body (afterBody isa summary n))
```

Fix `guardedLoopTree_eq_boundedWhileBehavior` proof similarly.

**Files touched:** CircularCoinduction.lean (~408-413, ~530+)

### Commit 4: Delete `ite'`

`ite'` (ProgramStructure.lean:278) is now redundant with `guardedChoice`.
Delete it. Check for any remaining uses.

**Files touched:** ProgramStructure.lean

### Commit 5 (OPTIONAL, LATER): Delete `choice` constructor

Only after ALL uses of `choice` are migrated and all proofs updated.
This is a bigger change — every pattern match on CompTree gains/loses a case.
May not be worth doing immediately if there's no pressing need.

**Decision point:** Sophie's call. May want to keep `choice` for expressiveness
(nondeterministic programs that aren't guarded) or delete for cleanliness.

## What This Enables

With guardedChoice as the primitive, the tree structurally enforces input-space
partitioning. This is the foundation for:

### Finding #4: Branch-set stabilization

ICTAC Lemma 1 (pairwise disjoint preconditions) says: if two pieces in the same
program share any input, they're identical. With guardedChoice, every choice
point partitions the state space via `guard` and `pc_not guard`. This gives us
structural disjointness for free — no need for the ugly `Fintype Sub` pigeonhole.

The argument (from ICTAC paper analysis, NOT verified in Lean):
1. All pieces from all depths live in `F_{while b p}` as a single object
2. Lemma 1 applies within that object → pieces with overlapping PCs are identical
3. Concrete periodicity (orbit_repetition) → depth-(K+1) piece shares input with
   depth-≤K piece
4. By Lemma 1 → same piece → branch set stabilization

**Critical subtlety:** Lemma 1 is intra-program. Works across depths only because
all are in the while-loop union. Need `guardedLoopDenotInf` or equivalent to
formalize this.

### Finding #5: Absorptive/pcSetoid bridge

Separate problem. Absorptive counts raw Branch syntax; pcSetoid is about states.
Need branch quotient/canonicalization. Not blocked on guardedChoice refactor.

## Open Questions

1. **How many places construct LoopSummary?** Determines propagation scope of
   `guard_complement` field. CHECK BEFORE STARTING.
2. **Weak vs strong complementarity?** `continues → pc_not exits` vs
   `continues ↔ ¬ exits` vs `continues = pc_not exits`. Start weak, strengthen
   if needed.
3. **Does `LoopSummary.Sound` need updating?** Currently requires
   `continues ∨ exits` (coverage). Complementarity would strengthen this to a
   partition. The two are compatible but `Sound` might want the complement field.
4. **Should `guard_complement` be equality (`continues = pc_not exits`)?**
   Equality is cleanest but requires `pc_not` to be involutive. Check
   SymbolicISA for `pc_not` properties.
5. **Is `choice` worth keeping?** For programs that genuinely have nondeterminism
   (concurrency, etc.), `choice` might still be useful. For our current scope
   (deterministic programs), it's dead weight.

## Review Protocol

Each commit gets a synchronous opus subagent review before proceeding to the next.
Review checks: builds, 0 sorries, 0 errors, 0 warnings, proof obligations
discharged correctly.

## Dependencies

```
Commit 1 (guard_complement field)
  ↓
Commit 2 (afterBody migration)    ← needs guard_complement for proof
  ↓
Commit 3 (guardedLoopTree migration) ← needs afterBody already migrated
  ↓
Commit 4 (delete ite')            ← independent, but cleaner after migration
  ↓
[Finding #4 work]                 ← needs guarded tree for ICTAC disjointness
```

Commits 1-3 are strictly sequential. Commit 4 is independent but ordered for
cleanliness. Finding #4 work is separate but enabled by this refactor.
