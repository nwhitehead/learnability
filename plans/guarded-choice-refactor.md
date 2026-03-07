# Plan: guardedChoice Refactor + LoopSummary Complementarity

## Status
- **Branch:** `ictac-computability`
- **Last clean commit:** `8704d210` — afterBody migrated to guardedChoice
- **Working copy:** CLEAN
- **Build:** 741 jobs, 0 sorries, 0 errors, 0 warnings

## Background

Sophie's insight: "CompTree should always have been guarded." Every actual use
of `choice` in the codebase is already guarded:
- `afterBody`: `choice (assert exits) (seq (assert continues) ...)`
- `guardedLoopTree`: same pattern
- `ite'` (ProgramStructure.lean:278): `choice (seq (assert φ) t₁) (seq (assert (pc_not φ)) t₂)`

`guardedChoice guard tThen tElse` was added in `f0e740f8`. Its semantics are
definitionally equal to `choice (seq (assert guard) tThen) (seq (assert (pc_not guard)) tElse)`.

## Completed Commits

### ✓ Commit 1: Add `guard_complement` field to LoopSummary (c973163f)
Added `guard_complement : ∀ s, isa.satisfies s continues → isa.satisfies s (isa.pc_not exits)`.
Zero propagation (LoopSummary is never instantiated). **Will be upgraded to
`guard_partition` (biconditional) in Commit 4 below.**

### ✓ Commit 2: Migrate `afterBody` to `guardedChoice` (8704d210)
afterBody now uses `.guardedChoice exits .skip (...)`. Proof uses `guard_complement`
to derive `satisfies s (pc_not exits)` from `satisfies s continues`. Builds clean.

## Semantic Bug (discovered attempting Commit 3)

Migrating `guardedLoopTree` to `guardedChoice` failed. The root cause is NOT
a missing field — it's a shifted-by-one bug in `whileBehavior`.

`whileBehavior` checks continues at the wrong indices:

```
Current:  ∀ k, k + 1 < n → satisfies (bodyEffect^[k + 1] s) continues
Correct:  ∀ k, k < n     → satisfies (bodyEffect^[k] s)     continues
```

Concretely:
- n=0: exits at s. Both agree. ✓
- n=1: current has NO continues check. Correct: continues at s. ✗
- n=2: current checks only at bodyEffect s. Correct: at s AND bodyEffect s. ✗

The current semantics doesn't check the loop condition before the first iteration.
A standard while loop checks before every iteration including the first.

**Why this blocks guardedLoopTree:** `guardedChoice exits` at the top level requires
`pc_not exits` to enter the loop. With correct semantics, n≥1 → continues at s →
pc_not exits at s (via guard_partition). With shifted semantics, no continues at s
for n=1, so no way to derive pc_not exits.

## Remaining Commits (Phase 1 continued)

### Commit 3: Fix whileBehavior semantics
**File:** CircularCoinduction.lean (~line 108-112, ~line 446-451)

Change `whileBehavior`:
```lean
-- old:
(∀ k, k + 1 < n → isa.satisfies (summary.bodyEffect^[k + 1] s) summary.continues) ∧
-- new:
(∀ k, k < n → isa.satisfies (summary.bodyEffect^[k] s) summary.continues) ∧
```
Same change in `boundedWhileBehavior`.

### Commit 4: Upgrade guard_complement → guard_partition
**File:** CircularCoinduction.lean (LoopSummary structure, ~line 74)

Replace one-directional `guard_complement` with biconditional:
```lean
guard_partition : ∀ s, isa.satisfies s continues ↔ isa.satisfies s (isa.pc_not exits)
```
Captures both disjointness (continues → ¬exits) and exhaustivity (¬exits → continues).
`LoopSummary.Sound`'s `continues ∨ exits` clause becomes derivable.

Fix `afterBody_behavior` proof to use `guard_partition` instead of `guard_complement`.

### Commit 5: Migrate guardedLoopTree to guardedChoice
**File:** CircularCoinduction.lean (~line 412-417)

Now possible with fixed semantics + guard_partition:
- Forward: pc_not exits → ¬exits (sat_not) → continues (guard_partition.mpr) →
  supplies continues at s for the corrected whileBehavior
- Backward: continues at s (k=0 of fixed whileBehavior) →
  pc_not exits (guard_partition.mp) → guardedChoice else branch

Fix `guardedLoopTree_eq_boundedWhileBehavior`.

### Commit 6: Fix stabilization_complete
**File:** CircularCoinduction.lean (~line 741-797)

Index adjustment for the shifted continues check. Orbit_repetition + periodicity
argument structure is the same; continues witness indices change.

### Commit 7: Delete `ite'`

`ite'` (ProgramStructure.lean:278) is redundant with `guardedChoice`. Delete it.

### Commit 8 (OPTIONAL, sophie's call): Delete `choice` constructor

Bigger change — every CompTree pattern match affected. Keep for expressiveness
(nondeterministic programs) or delete for cleanliness. Sophie decides.

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

1. **Is `choice` worth keeping?** For programs that genuinely have nondeterminism
   (concurrency, etc.), `choice` might still be useful. For our current scope
   (deterministic programs), it's dead weight.

---

## Phase 2: Finding #4 — Branch-Set Stabilization

With guarded trees, ICTAC Lemma 1 (pairwise disjoint preconditions) gives us:
pieces with overlapping PCs are identical. Combined with `orbit_repetition`,
this closes the gap from concrete periodicity to symbolic branch-set
stabilization. Check ICTAC-DenotSymbEx Coq code for existing mechanization
before writing own.

**File:** `CircularCoinduction.lean` (new theorems)

---

## Phase 3: Finding #5 — Absorptive/pcSetoid Bridge

Absorptive counts raw Branch syntax; pcSetoid is about states. Need branch
quotient or canonicalization so Absorptive operates on semantic equivalence
classes. This is proof solidity — must be done before e2e while context is
fresh.

**Files:** `CircularCoinduction.lean`, possibly `Quotient.lean`

---

## Phase 4: Noncomputable Audit

Categorize all 15 `noncomputable` defs. Fix ones on the constructive path
(CompTree → denot → convergence → oracle → LTS). Must clear this BEFORE
e2e to avoid discovering gremlins mid-integration.

Known constructive-path issues:
- `finsetQuery`/`finsetOracle`/`treeOracle` in EffectiveObservability.lean
  (Nonempty.choose → Finset.min' or similar)
- `pcClosure`/`pcSignature` in Quotient.lean (classical fixpoint → bounded iteration)

Known genuinely-noncomputable (not on constructive path):
- `quotientSignature` (Quotient.lift architectural limitation)
- `abstractStateFintype` (noncomputable injection)

**Deliverable:** Categorization doc + fixes for constructive-path items.

---

## Phase 5: End-to-End — pcode SymbolicISA + Manual Instantiation

The stack:
1. **Binary → pcode/VEX** — angr (exists, battle-tested)
2. **pcode CFG → CompTree** — extract program structure (NOT done, bounded work)
3. **CompTree → Finset Branch** — `denot` (DONE, proven sound+complete)
4. **Loop convergence** — `loopBranchSet` + `stabilization_complete` (DONE)
5. **Oracle refinement** — `oracleStep` etc. (DONE)

### SymbolicISA for pcode
~30 core operations. Sub = pcode variable assignments, PC = constraints on
pcode variables. One manual instantiation first — no tooling until we've
done it by hand once.

### Architecture
Lean proves the METHOD correct (composition + convergence guarantees).
angr provides runtime muscle (fast symex, binary lifting, CFG extraction).
The naive Lean symex (`denot`) is the reference implementation / correctness
certificate, not the production engine. Practitioners trust angr is correct
enough for the base case; Lean proves the global guarantees compose on top.

### Self-verification opportunity
The technique itself can verify that our pcode SymbolicISA instantiation is
bisimilar to the reference pcode semantics.

---

## Execution Order

```
Phase 1: guardedChoice refactor     ← IN PROGRESS (Commits 1-2 done, 3-7 remain)
  ↓
Phase 2: Finding #4                 ← ICTAC disjointness on guarded trees
  ↓
Phase 3: Finding #5                 ← branch quotient, proof solidity
  ↓
Phase 4: Noncomputable audit+fix    ← clear minefield before e2e
  ↓
Phase 5: End-to-end                 ← pcode ISA + CFG→CompTree + reality
```

Phases 1-3 are proof solidity (do while context is fresh).
Phase 4 is computability (do before e2e to avoid chaos).
Phase 5 is where everything meets reality.

## Review Protocol

Each commit gets a synchronous opus subagent review before proceeding to the next.
Review checks: builds, 0 sorries, 0 errors, 0 warnings, proof obligations
discharged correctly.

## Dependencies

```
✓ Commit 1 (guard_complement field)
  ↓
✓ Commit 2 (afterBody migration)
  ↓
Commit 3 (fix whileBehavior)       ← semantic bug fix
  ↓
Commit 4 (guard_partition upgrade)  ← enables guardedLoopTree migration
  ↓
Commit 5 (guardedLoopTree)         ← needs fixed semantics + guard_partition
  ↓
Commit 6 (fix stabilization)       ← needs fixed semantics
  ↓
Commit 7 (delete ite')             ← independent cleanup
  ↓
[Phase 2: Finding #4]
[Phase 3: Finding #5]
[Phase 4: Noncomputable audit]
[Phase 5: End-to-end pcode ISA]
```
