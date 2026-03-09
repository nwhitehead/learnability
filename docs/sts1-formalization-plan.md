# STS1 Formalization Plan

## Reference

Henzinger, Majumdar, Raskin. "A Classification of Symbolic Transition Systems."
ACM TOCL 6(1), January 2005. doi:10.1145/1042038.1042039.

## Background: The STS Hierarchy

HMR05 classifies infinite-state symbolic transition systems into five classes
(STS1-STS5) based on which state equivalence has finite index. Each class
corresponds to a closure algorithm and a decidable logic:

| Class | Equivalence | Closure ops | Decidable logic |
|-------|-------------|-------------|-----------------|
| STS1 | bisimilarity | Pre + And + Diff | full mu-calculus (CTL, CTL*) |
| STS2 | similarity | Pre + And | negation-free mu-calculus |
| STS3 | trace equivalence | Pre + And(sigma, p in P) | LTL, omega-regular, Buchi |
| STS4 | distance equivalence | Pre only | conjunction/disjunction-free mu-calculus |
| STS5 | bounded reachability | Pre (weaker termination) | reachability |

Strict containment: STS1 < STS2 < STS3 < STS4 < STS5. Each class is
characterized by which boolean operations the closure algorithm requires.
Fewer operations = bigger class = weaker logic.

For deterministic systems, bisimilarity = trace equivalence, so STS1 = STS3.
Our current system (deterministic loop body) is in this regime. But
concurrency introduces nondeterminism, making the distinction real.

## What We Currently Have

### Proved and compiled

1. **Congruence theorems** (Quotient.lean):
   - `pcEquiv_branch_firesWith`: if s1 ~= s2 and branch b fires from s1, b fires from s2
   - `pcEquiv_eval_subWith`: if s1 ~= s2, successors under b are equivalent
   - These ARE the bisimulation conditions for the branch-induced system.

2. **Finiteness** (Quotient.lean):
   - `abstractState_card_bound`: quotient size <= 2^|closure|
   - `pcClosureSeq_stabilizes`: closure computation terminates

3. **Compression theorem** (VexWitness.lean):
   - `whileLoopBranchingUnrollBound_of_branchClassesStable`
   - Branch-class stability -> bounded witness covers loop observations
   - Works at observation level (STS3-flavored proof technique)

4. **Explicit closure refactor** (Quotient.lean, VexWitness.lean):
   - `pcSetoidWith`, `pcEquiv_branch_firesWith`, `pcEquiv_eval_subWith`
   - No [Fintype (SymPC Reg)] requirement

5. **Cross-bisimulation framework** (Quotient.lean):
   - `CrossBisimulation`, `quotient_forward`, `quotient_backward`
   - `quotient_bisimulation`: Sound + Complete -> CrossBisimulation

### The current gap

The compression theorem proves observation-level coverage (STS3). The
congruence theorems prove the bisimulation conditions (STS1 ingredients).
But there is no single theorem that says "this system is STS1" — the
ingredients exist but aren't composed.

## Why STS1 Matters

For sequential deterministic loops: STS1 = STS3, so no practical difference.

For future work with concurrency (interleaving, interrupts, nondeterministic
environments): STS1 gives full mu-calculus model checking. STS3 gives only
LTL. The difference is branching-time properties:

- CTL: EF(EX bad) — "can the system reach a state where it can CHOOSE to violate the invariant?"
- CTL: AG(EF good) — "from every reachable state, the system can recover"
- These require the full branching structure that bisimilarity preserves.

Investing in STS1 now avoids rework when adding concurrency.

## Formalization Options

### Option A: One-step body STS1 (~60-80 lines) [RECOMMENDED]

Add to Quotient.lean (or a new file):

```lean
-- The concrete body transition (one loop iteration under the continue guard)
def bodyTransition (isa : SymbolicISA ...) (loop : LoopSummary ...)
    (s s' : State) : Prop :=
  isa.satisfies s loop.continues /\ s' = loop.bodyEffect s

-- PC-equivalence is a bisimulation of bodyTransition
-- Proof: from pcEquiv_branch_firesWith (continues guard is in the model,
-- so equivalent states agree on continues) + pcEquiv_eval_subWith
-- (successors under the body summary are equivalent) + model completeness
-- (every concrete body step is witnessed by some branch).
theorem pcEquiv_bisimulates_bodyTransition
    (model : Finset (Branch Sub PC))
    (closure : Finset PC)
    (h_contains : forall b in model, b.pc in closure)
    (h_closed : forall b in model, forall phi in closure, pc_lift b.sub phi in closure)
    (h_complete : forall s, satisfies s loop.continues ->
        exists b in model, satisfies s b.pc /\ eval_sub b.sub s = loop.bodyEffect s) :
    -- Forward simulation: if s1 ~= s2 and bodyTransition s1 s1',
    -- then exists s2' with bodyTransition s2 s2' and s1' ~= s2'
    ...

-- The system is STS1: bisimilarity has finite index <= 2^|closure|
theorem bodyTransition_finiteBisimilarityQuotient ...
```

**What this gives**: a clean, extractable statement that the loop body transition
system has a finite bisimilarity quotient. The compression theorem is a
separate corollary (finite quotient -> bounded orbits -> bounded loop
iterations).

**What it needs**: a completeness hypothesis for the branch model w.r.t.
one-step body transitions. `BodyPathStepRealizable` from VexWitness.lean
provides this — it says every concrete body step has a matching summary.

**Dependencies**: congruence theorems (done), finiteness bound (done),
model completeness bridge (BodyPathStepRealizable, done as hypothesis).

### Option B: Determinism lemma (~20 lines) [SUBSUMED BY A]

```lean
theorem trace_eq_bisimilarity_of_deterministic
    (h_det : forall s, Set.Subsingleton (delta s)) :
    trace_equivalence S = bisimilarity S
```

States that for deterministic systems, STS3 = STS1. Then our STS3 result
(compression theorem) immediately gives STS1.

**Skip this if doing Option A.** Option A gives a direct STS1 proof that
doesn't go through trace equivalence. Option B is only useful as a cheap
shortcut when you don't want to do the bisimulation proof directly.

### Option C: Parametric HMR05 framework (~200-300 lines)

```lean
structure SymbolicTransitionSystem where
  Q : Type*
  delta : Q -> Set Q
  R : Type*
  ext : R -> Set Q
  P : Finset R
  -- HMR05 Definition 1 conditions:
  -- (1) P covers Q
  -- (2) Pre computable
  -- (3) And computable
  -- (4) Diff computable
  -- (5) Empty decidable
  -- (6) Member decidable

-- Define all five equivalences (bisimilarity through bounded-reachability)
-- Define all five closure algorithms (Closure1 through Closure5)
-- Prove: Closure_i terminates iff S in STS(i)

-- Instantiate for our system
instance vexBodySTS (Reg : Type) [DecidableEq Reg] [Fintype Reg]
    (loop : VexLoopSummary Reg) : SymbolicTransitionSystem where
  Q := ConcreteState Reg
  delta := fun s => if satisfies s loop.continues
                    then {loop.bodyEffect s} else {}
  R := SymPC Reg
  ext := fun phi => {s | evalSymPC s phi}
  P := (branchingLoopModel loop bodyPaths).image (·.pc)
```

**What this gives**: a universal framework that directly instantiates HMR05.
Works for future concurrent systems. Directly citeable in the paper.
The STS1 result falls out of the instantiation + Theorem 1A.

**Effort**: probably two dedicated sessions. Most of the work is the framework
itself (defining the five equivalences, the five algorithms, the five
characterization theorems). The instantiation is relatively easy given
what we already have.

## Plan

0. **Rebase %43 into default** (PREREQUISITE). The `learnability-pc-convergence`
   workspace has 3 commits ahead of the fork point (`8a272beb`):
   - `870ea1f4` generalize quotient congruence over explicit closures
   - `d0f2dad0` rewire branching witness compression to explicit closures
   - (empty working copy `5c42cc0b`)

   The `default` branch also has 3 commits from that same fork point:
   - `6ba3dc7c` derive loop witness coverage from body-effect path realizability
   - `30d3a23c` document remaining deterministic loop witness gap
   - `d9281198` document STS1 formalization plan

   Both branches modify `VexWitness.lean` — conflict resolution needed.
   The %43 work (explicit closures, `pcSetoidWith`, `...With` congruence
   theorems) is a hard prerequisite for Option A.

1. **Option A**: Direct one-step body STS1. ~60-80 lines.
2. **Checkpoint**: verify it compiles, review with Codex.
3. **Later**: Option C as the paper-level framework. Depends on whether
   the workshop submission needs it or whether citing HMR05 suffices.

## Relationship to Existing Theorems

From Quotient.lean (compose directly):
- `pcEquiv_branch_firesWith` -> same branch fires from equivalent states
- `pcEquiv_eval_subWith` -> successors equivalent
- `abstractState_card_bound` -> finite quotient

From VexWitness.lean (provide hypotheses):
- `BodyPathStepRealizable` -> model completeness for body transitions
- `BranchClassesStable` -> loop-level stabilization
- `PCObserveInvariant` -> observation respects equivalence

From Bisimulation.lean (framework):
- `CrossBisimulation` -> the cross-system bisimulation structure
- `quotient_bisimulation` -> Sound + Complete -> CrossBisimulation

The key composition: BodyPathStepRealizable provides the completeness
hypothesis that `quotient_forward` needs (modulo the QuotientComplete
reformulation), and the congruence theorems provide the bisimulation
conditions that make the quotient well-defined.

## Note on Observation and Losslessness

HMR05 is a classification framework (analogous to the Chomsky hierarchy),
not an algorithm paper. The observation function's injectivity is orthogonal
to the STS classification:

- If observe is injective: trace equivalence = bisimilarity trivially
  (traces determine full state), but the quotient is trivial (each class
  is a singleton). Not useful for the symbolic approach.
- If observe is lossy: the STS classification distinguishes which
  properties are decidable. The quotient is nontrivial and meaningful.

For concolic execution (our primary mode): concrete traces are lossless,
but the symbolic layer (path constraints, witness construction for
alternate branches) operates on the quotient. The congruence theorems
bridge these two levels — they show that the symbolic quotient respects
the concrete transitions regardless of observation granularity.

The congruence theorems are the load-bearing structure, not the
observation function. Observation is a parameter the theorems are
generic over.
