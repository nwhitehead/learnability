# Learnability Framework: Next Phase Strategy

## Context
Phases 5-9 (front half) complete. The framework proves: program → convergent
branch model (= symbolic transformer / LTS) via oracle-guided refinement.

Key gaps identified:
- 15 `noncomputable` definitions across the codebase (computability gap)
- No review standards for computability
- Loop detection from binaries untested (LoopSummary assumes single-branch body)
- No executable pipeline (proofs only, no running code)

## Ordering Principle
Riskiest/most uncertain first. Quick enabling work before risky spikes.

---

## Phase A: Code Review Standards (quick, enabling)

**Goal:** Document review gates so future work doesn't accumulate the same defects.

New gates (in addition to existing 0-sorries, totality):
1. **No unjustified `noncomputable`** — if the algorithm is decidable, the code
   must compute. Every `noncomputable` needs a comment justifying why.
2. **No existence-only proofs for runnable things** — `∃ x, P x` is not acceptable
   when the point is to produce `x`. Use `Decidable`, `DecidableEq`, explicit
   construction.
3. **No `Classical.choice` in computational paths** — decidable instances only.
   Classical reasoning is fine in pure proof context (showing a property holds),
   not in definitions that should execute.
4. **Computational mapping** — every definition/theorem should have a clear answer
   to: "what computational content does this correspond to?" or "what
   meta-property of an implementation does this capture?" If neither, justify why
   it's in the codebase.

Deliverable: Update learnability CLAUDE.md or a REVIEW_STANDARDS.md that review
agents are pointed at.

**Risk: none. Effort: ~30min.**

---

## Phase B: Back-Edge Loop Detection Spike (de-risk)

**Goal:** Determine whether CFG back-edge loop detection composes cleanly with
our framework, and identify what framework extensions (if any) are needed.

### Specific risks to probe:

1. **Single-branch LoopSummary vs multi-path loop bodies.**
   `LoopSummary.body : Branch Sub PC` — a single branch. Real loop bodies have
   if-then-else, multiple paths. `CompTree.boundedIter` already takes a CompTree
   body. Question: do we need to extend LoopSummary to `body : CompTree Sub PC`
   (or `body : Finset (Branch Sub PC)`)? Or is LoopSummary only for the
   mathematical framework and we use `boundedIter` directly for real loops?

2. **Multi-exit loops (break/early-return).**
   Can we represent `while (cond) { if (x) break; ... }` cleanly? The exit
   condition in LoopSummary is checked post-body, but breaks exit mid-body.
   CompTree.choice can model this, but does boundedIter handle it?

3. **Irreducible CFGs.**
   Most compiled code has reducible CFGs (structured programming → reducible).
   But goto-heavy C, some optimized code, and hand-written assembly can produce
   irreducible CFGs where back-edge analysis doesn't cleanly identify loops.
   How common is this in practice for our target domain (parsers)?

4. **Nested loops.**
   Our framework should handle these via recursive CompTree structure, but verify.

5. **Lucanu et al. and binary-level work.**
   Do Lucanu/Rusu/Arusoaie or their citers address loop identification from
   binaries? Or do they all assume syntactic loop structure?

### Approach:
- Take a small real binary (a simple parser, maybe one from the FCA corpus)
- Run angr on it, extract CFG, identify back edges
- Attempt to construct loop summaries / CompTree from the back-edge analysis
- Document where the framework does/doesn't fit
- Literature check on Lucanu citations re binary-level

**Risk: medium. This is the thing most likely to require framework extension.
Effort: 1-2 sessions.**

---

## Phase C: Fix EffectiveObservability Computability (concrete fix)

**Goal:** Replace `noncomputable` in EffectiveObservability.lean with computable
alternatives.

The 3 noncomputables there (`finsetQuery`, `finsetOracle`, `treeOracle`) all
stem from `Nonempty.choose`. Fix: use `Finset.min'` with a linear order on
Branch, or use decidable membership + `Finset.toList`.

Requires adding `[LinearOrder (Branch Sub PC)]` or `[Ord (Branch Sub PC)]` to
Branch, or using a different selection strategy.

Build, verify 0 warnings, commit, review.

**Risk: low. Effort: ~1 hour.**

---

## Phase D: Noncomputable Audit + Excision Plan

**Goal:** Audit all 15 noncomputables, categorize each, plan the fix.

Categories:
- **Fixable (decidable algorithm, wrong encoding):** e.g., finsetQuery
- **Needs refactoring (structural issue):** e.g., refineStep using Classical
- **Justified (pure proof context):** some may be legitimately non-computational

For each: document what computational content it SHOULD map to, and what the fix
path is. Some may require significant restructuring (refineStep is the big one).

This becomes its own execution phase (or set of phases) afterward.

**Risk: low (audit), medium-high (fixes). Effort: audit ~1 session, fixes TBD.**

---

## Phase E: Executable Test — End-to-End on a Toy Target

**Goal:** Actually run the pipeline on something real. A tiny parser binary,
angr as symex engine, branch collection, convergence check.

This is where all the pieces come together:
- SymbolicISA instantiated for the target architecture (ARM/x86, using existing
  formal models + LLM assistance)
- angr providing the oracle (counterexample paths)
- Branch encoding from angr paths
- Convergence loop
- Output: the recovered LTS

This validates whether the framework is actually usable, not just provable.

**Risk: high (first end-to-end test). Effort: multiple sessions.**

---

## Execution Order

```
A (review standards)           ← quick, enables everything
  ↓
B (back-edge spike)            ← de-risk, may reshape later phases
  ↓  (in parallel: Lucanu citation search)
C (fix EffectiveObservability) ← concrete, bounded
  ↓
D (noncomputable audit)        ← scope the excision work
  ↓
E (end-to-end test)            ← validates the whole thing
```

Phases B and C can overlap if B doesn't require framework changes that touch
EffectiveObservability. D depends on C (we want the pattern established before
auditing everything). E depends on all of the above.
