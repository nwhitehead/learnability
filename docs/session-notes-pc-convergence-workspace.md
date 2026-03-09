# Session Notes: PC-Stabilization Convergence Workspace

This file records the conceptual context for the work done in this workspace on the
PC-stabilization route for loop-witness completeness.

## 1. Original task

The original task was to pursue the alternative loop-completeness route based on
PC-stabilization with branching witnesses, not the parallel deterministic
`whileBehavior` route.

The user provided these constraints and objectives:

- Read and understand:
  - `SymExec/Quotient.lean`
  - `Instances/ISAs/VexWitness.lean`
  - `Instances/ISAs/VexModelEq.lean`
  - `SymExec/ModelEq.lean`
  - `docs/witness-convergence-plan.md`
- Add a branching witness family:
  - `branchingLoopWitness : Finset (List (Block Reg)) -> Nat -> Finset (List (Block Reg))`
- Define `LiveBranchClass` using the existing quotient/signature machinery.
- Prove the compression theorem idea:
  - repeated PC-class implies no genuinely new loop behavior
  - use `pcEquiv_branch_fires`
  - use `pcEquiv_eval_sub`
  - package the result into loop witness completeness
- Add everything additively.
- Keep the build green.
- Use `lake build`.

The initial implementation I landed added the branching witness layer, the class
machinery, and the completeness packaging in `Instances/ISAs/VexWitness.lean`.
That first version compiled and was committed as:

- `8a272beb6ba0` `add branching loop witness stabilization layer`

That first version turned out to carry a bad assumption:

- `[Fintype (SymPC Reg)]`

This notes file is mainly about why that was wrong and how it was removed.

## 2. The `[Fintype (SymPC Reg)]` problem

The problem is that `SymPC Reg` is not actually finite for the real VEX ISA.

`SymPC Reg` is defined as an inductive symbolic predicate language with constructors:

- `true`
- `eq`
- `and`
- `not`

The important point is that `eq` contains symbolic expressions, and symbolic expressions
are themselves recursively generated. Even if `Reg` is finite, the term language is a
free algebra with unbounded nesting:

- `true`
- `not true`
- `not (not true)`
- `and true true`
- `and true (and true true)`
- and so on

There is no finite bound on term depth, so there are infinitely many distinct
`SymPC Reg` terms. That means:

- a global `Fintype (SymPC Reg)` instance is not available
- more importantly, it would be mathematically wrong to pretend one exists

So the first version of the branching-witness code was not suitable for rebasing into
main, because it relied on an assumption that is unsatisfiable for the real VEX PC
language.

## 3. Alternatives considered, including what failed

### 3.1 Keep `[Fintype (SymPC Reg)]` and treat it as a future abstraction hook

This was the first implementation. It made the code easy to write because the existing
`Quotient.lean` API was built around:

- `pcSetoid`
- `pcEquiv_branch_fires`
- `pcEquiv_eval_sub`
- `pcSignature`
- `equiv_of_pcSignature_eq`

Those all sat on top of `pcClosure` and therefore required `[Fintype PC]`.

Why it was rejected:

- it is not true for real `SymPC Reg`
- it would block rebasing to main
- it hid the real issue instead of fixing it

### 3.2 Re-prove the congruence lemmas locally inside `VexWitness.lean`

I considered bypassing `Quotient.lean` entirely and reproving the needed facts in
`VexWitness.lean` with an explicit closure.

Why it was rejected:

- it would duplicate core reasoning already present in `Quotient.lean`
- it would create two parallel versions of the same quotient theory
- it would make maintenance worse
- it would be the wrong factoring: the generalization belongs in `Quotient.lean`

### 3.3 Push everything to `Set PC` rather than `Finset PC`

This would avoid some finiteness machinery, but it breaks the signature side of the
story. The whole point of `pcSignature` is:

- pick a finite closure
- filter it by the PCs satisfied by a state
- compare those finite signatures

Using `Set PC` would lose the finite-signature object that the proofs are organized
around.

Why it was rejected:

- it would be a larger redesign
- it would move away from the existing shape of the quotient proofs
- it would complicate the witness code for no gain

### 3.4 Re-encode the closure as a finite subtype and build a new ISA over it

Another theoretical option was:

- take `closure : Finset PC`
- work over the subtype `Subtype fun φ => φ ∈ closure`
- rebuild the needed symbolic API over that finite subtype

Why it was rejected:

- far too invasive for the goal
- not mechanical
- would require substantially more proof infrastructure than the user requested

### 3.5 Change the top-level branching theorem to depend on `h_closed`/`h_contains` everywhere

I considered pushing the explicit closure hypotheses all the way to every theorem in
`BranchClassCompression`.

What actually happened:

- the helper congruence theorems do take the explicit closure hypotheses where needed
- the final coverage theorem does not need all of them, because it compresses by
  observation equality rather than by replaying every control-flow fact

This is an important subtlety:

- some closure hypotheses are structurally necessary for the congruence helpers
- they are not all necessary in the final top-level coverage theorem as currently stated

### 3.6 Mechanical dead end during the refactor

During the `Quotient.lean` refactor I temporarily made a bad scope change:

- I accidentally removed `[Fintype PC]` from `section PCClosure`
- and still had `[Fintype PC]` attached to `section PCEquiv`

This produced confusing errors:

- failures around `Finset.univ` in the closure-construction section
- synthetic `sorry` warnings because Lean inserted placeholders after the earlier errors

That was not a design problem. It was just a bad section-scoped edit and was fixed by
patching the exact section headers.

## 4. Why the explicit closure pattern was the right fix

The user-provided fix was right because the actual logical dependency of the congruence
proofs is not:

- "the whole PC type is finite"

It is:

- "we have a finite set `closure : Finset PC`"
- "the branch PCs we care about are inside it"
- "it is closed under `pc_lift` for the model branches"

That is exactly the shape used in the proofs:

- branch firing only needs to know `b.pc ∈ closure`
- successor congruence only needs to know `pc_lift b.sub φ ∈ closure`
- signature equivalence only needs a finite `closure` to filter against

So the explicit closure pattern was the right shape because it:

- removes the false global finiteness assumption
- preserves the original proof structure almost verbatim
- keeps the general theory in `Quotient.lean`
- lets downstream code choose whatever finite closure it wants
- keeps the old `[Fintype PC]` API intact as wrappers

That last point mattered. Existing finite-PC uses of `Quotient.lean` did not need to be
rewritten. The old API still exists, but now it is layered on top of the closure-
parameterized core.

## 5. What was tricky about rewiring `VexWitness.lean`

Several things were easy to get subtly wrong.

### 5.1 `LiveBranchClass.Realizes` did not actually need the loop summary

After switching from `pcSignature` to `pcSignatureWith`, the `Realizes` predicate only
needed:

- `bodyPaths`
- `closure`
- the class
- the concrete state

It no longer needed the loop summary itself. Keeping the old parameter produced unused
variable warnings.

The same thing happened for `PCObserveInvariant`:

- after moving to `pcSetoidWith closure`, it no longer needed `loop` or `bodyPaths`
- leaving them in place caused warning noise

Those were cleaned up so the final build is warning-free.

### 5.2 The helper theorems and the top-level theorem need different assumptions

The congruence helpers genuinely need explicit closure facts:

- `summary_enabled_of_realizes` needs a containment hypothesis
- `successor_pcEquiv_of_realizes` needs a closure-under-lifting hypothesis

But the final top-level coverage theorem,
`whileLoopBranchingUnrollBound_of_branchClassesStable`, no longer uses those helper
theorems directly. The coverage proof compresses an observation by:

- finding an earlier state with the same explicit signature
- using observation invariance over `pcSetoidWith closure`
- using the bounded witness-reachability theorem

That proof does not itself need to replay branch firing or successor congruence, even
though the helper theorems are still present and correct.

### 5.3 The final coverage theorem compresses by observation, not by re-establishing a full earlier while-exit

An important design choice in the current code:

- the coverage theorem does not prove the earlier equivalent state is itself an earlier
  `whileBehavior` exit witness
- instead it proves the branching witness can realize an earlier state with the same
  observation

This is enough for `BranchingLoopUnrollBound`, because that obligation is only about
coverage of observed behavior, not about re-deriving the concrete loop semantics. The
soundness half remains a separate assumption.

This is why the top-level theorem is lighter than an attempt to prove "full concrete tail
replay."

### 5.4 The witness-reachability proof is easier if the witness family is built by prefixing

`branchingLoopWitness` is defined recursively so that at depth `n + 1` it adds:

- all shorter paths
- all `body ++ tail` where `body ∈ bodyPaths` and `tail ∈ branchingLoopWitness n`

That shape matches the inductive proof of
`branchingLoopWitness_reaches_iterate`:

- pick the first body-step representative
- recurse on the tail from the deterministic next state

That was a deliberate choice. Appending at the end would have made the proof more awkward.

## 6. Structure of the `...With` variants vs the originals

The `...With` variants are structurally almost identical to the originals.

### 6.1 `pcSetoidWith`

Original:

- `pcSetoid model := pcEquiv over pcClosure model`

New:

- `pcSetoidWith closure := pcEquiv over explicit closure`

Design point:

- the relation itself never needed `pcClosure`
- only the old convenience API did

### 6.2 `pcEquiv_branch_firesWith`

Original proof input:

- `hb : b ∈ model`
- derive `b.pc ∈ pcClosure model` via `pcClosure_contains_model_pcs`

New proof input:

- `hb_mem : b.pc ∈ closure`

Same proof body:

- apply equivalence at `b.pc`

### 6.3 `pcEquiv_eval_subWith`

Original proof input:

- `hb : b ∈ model`
- derive closure of lifted PCs via `pcClosure_closed`

New proof input:

- `hb_closed : forall φ ∈ closure, pc_lift b.sub φ ∈ closure`

Same proof body:

- use `sat_lift`
- translate satisfaction through `pc_lift`
- apply equivalence on the lifted PC

### 6.4 `pcSignatureWith`

Original:

- filter `pcClosure isa model`

New:

- filter explicit `closure`

This is the right abstraction boundary:

- the signature concept depends on a finite closure
- not on how that closure was obtained

### 6.5 `equiv_of_pcSignature_eqWith`

Original:

- from equal filtered signatures over `pcClosure isa model`, derive `pcSetoid isa model`

New:

- same exact argument over explicit `closure`

Again, the proof never fundamentally needed global `Fintype PC`; it only needed a
finite `Finset PC` to filter against.

### 6.6 Wrappers

The old finite-PC theorems now remain as wrappers:

- `pcSetoid`
- `pcEquiv_branch_fires`
- `pcEquiv_eval_sub`
- `pcSignature`
- `pcSignature_eq_of_equiv`
- `equiv_of_pcSignature_eq`

Each of these simply feeds `pcClosure isa model` into the explicit-closure core.

That kept the rest of the file and the other downstream files stable.

## 7. Things explored or considered that are not in the final commits

### 7.1 The original finite-PC branching layer commit

This exists in history as:

- `8a272beb6ba0` `add branching loop witness stabilization layer`

It compiled and was internally coherent, but it depended on the wrong assumption:

- `[Fintype (SymPC Reg)]`

It should be treated as superseded by the next two commits.

### 7.2 Use of control-guard branches in the top-level compression theorem

I originally expected the final coverage theorem to need explicit use of:

- continue/exit guard membership in the loop model
- `pcEquiv_branch_firesWith` on those guard branches

Those guard-branch helpers still make sense conceptually, and the loop model still
contains the guards, but the final coverage theorem does not currently need them.

The final proof only needs:

- earlier state with the same explicit signature
- observation invariance on that explicit setoid
- bounded branching-witness reachability

So there is a gap between "the conceptual story I first expected" and "the minimal proof
actually needed for the current theorem."

### 7.3 A stronger theorem shape was considered

I considered making the top-level theorem prove something closer to:

- if a live class repeats, then the entire remaining loop tail can be replayed from the
  earlier state

That would have forced much heavier use of the one-step congruence lemmas in the final
packaging theorem itself.

I did not push that through in this session because:

- the current `BranchingLoopUnrollBound` target only needs observed-behavior coverage
- the lighter theorem is enough for the current witness-completeness packaging

If a future session wants a stronger semantic compression theorem, the helper lemmas are
already there to support it.

### 7.4 VCS note

This repository is a `jj` repository, not a `git` repository.

Early in the session I probed with `git status` and got:

- `fatal: not a git repository`

No git writes happened. After that, all commits were made with `jj commit`.

Also note:

- `jj describe` only renames the current mutable working-copy change
- `jj commit` is what actually finalizes the current work and creates a fresh working copy

This mattered during the session and is worth remembering for future work.

## 8. Current codebase state

As of the end of this session:

- the code builds cleanly
- there are no warnings from the code changes
- the working copy is clean apart from whatever change this notes file introduces before
  its own commit

The relevant commits produced in this session are:

- `870ea1f40523` `generalize quotient congruence over explicit closures`
- `d0f2dad0450d` `rewire branching witness compression to explicit closures`

Important current facts:

- `SymExec/Quotient.lean` now supports explicit finite closures without requiring
  `[Fintype PC]` for the congruence/signature layer
- the old finite-PC API still exists as wrappers
- `Instances/ISAs/VexWitness.lean` no longer requires `[Fintype (SymPC Reg)]`
  in the BranchClassCompression section
- the branching witness layer now carries `closure : Finset (SymPC Reg)` explicitly

Verification status at the end of the session:

- `lake build SymExec.Quotient` passed after the refactor
- `lake build Instances.ISAs.VexWitness` passed after the rewiring
- full `lake build` passed after each atomic commit

There are no known compile failures left from this session.

## Practical advice for the next session

If the next session continues the PC-stabilization route, the likely next theorem boundary
is not this refactor. That part is done. The next interesting question is:

- what specific finite closure should be used in the VEX loop setting
- how should `h_closed` and `h_contains` be discharged for the chosen
  `branchingLoopModel`

In other words, the closure plumbing is now explicit and honest. The next step is to
instantiate it well, not to redesign it again.
