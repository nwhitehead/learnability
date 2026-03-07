import Composition

/-!
# Program Structure — Composition Trees

Composition trees encode program structure with ICTAC-style primitive leaves.
Two denotations:

1. **Symbolic denotation** (`denot`): CompTree → Finset Branch.
   Recursive via Phase 6 composition operators.

2. **Concrete denotation** (`treeBehavior`): CompTree → (State → State → Prop).
   Structural recursion: skip = identity, assign = eval_sub, etc.

## The Core Theorem

```
denot_sound ∧ denot_complete
```

Sound ∧ Complete for `denot tree` w.r.t. `treeBehavior tree`, by structural
induction on the tree. Base cases from SymbolicISA axioms. Inductive cases
from Phase 6 composition laws.

## Structural Bound

`bound tree` gives an a priori bound on `(denot tree).card`, computable
BEFORE running symbolic execution.

## ICTAC Correspondence

| ProgramStructure.lean | ICTAC |
|---|---|
| `CompTree.skip` | `PSkip` |
| `CompTree.assign` | `PAss` |
| `CompTree.assert` | guard (part of `PIf`) |
| `CompTree.seq` | `PSeq` |
| `CompTree.choice` | `PCh` |
| `CompTree.boundedIter` | unrolled `PWhile` |
| `denot` | `denot__S` |
| `treeBehavior` | `denot_fun_nondet` |
| `denot_sound ∧ denot_complete` | Theorem 2: `SE_correct ∧ SE_complete` |
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Composition Trees -/

/-- Program structure tree. Primitive leaves correspond to ICTAC primitives.

    Note: `ite` (if-then-else) is not a primitive — it encodes as
    `choice (seq (assert φ) t₁) (seq (assert (pc_not φ)) t₂)`.
    This matches ICTAC's treatment: `PIf b p₁ p₂ = PCh (PSeq (PGuard b) p₁) (PSeq (PGuard (BNot b)) p₂)`. -/
inductive CompTree (Sub PC : Type*) where
  /-- Identity: no state change. ICTAC: `PSkip`. -/
  | skip : CompTree Sub PC
  /-- Apply a substitution. ICTAC: `PAss`. -/
  | assign (σ : Sub) : CompTree Sub PC
  /-- Guard: identity, gated by path condition. ICTAC: `PGuard`. -/
  | assert (φ : PC) : CompTree Sub PC
  /-- Sequential composition. ICTAC: `PSeq`. -/
  | seq (t₁ t₂ : CompTree Sub PC) : CompTree Sub PC
  /-- Nondeterministic choice. ICTAC: `PCh`. -/
  | choice (t₁ t₂ : CompTree Sub PC) : CompTree Sub PC
  /-- Guarded choice: if guard holds take tThen, if pc_not guard holds take tElse.
      The guard PC lives in the tree, structurally enforcing that the two branches
      partition the input space. Equivalent to `choice (seq (assert guard) tThen)
      (seq (assert (pc_not guard)) tElse)` but as a primitive.
      ICTAC: `PIf b p₁ p₂`. -/
  | guardedChoice (guard : PC) (tThen tElse : CompTree Sub PC) : CompTree Sub PC
  /-- Bounded loop: execute body at most n times.
      Each iteration can either continue or exit nondeterministically. -/
  | boundedIter (body : CompTree Sub PC) (n : ℕ) : CompTree Sub PC
  deriving DecidableEq

namespace CompTree

variable {Sub PC State : Type*}

/-! ## Symbolic Denotation -/

/-- Symbolic denotation: CompTree → Finset Branch.
    ICTAC: `denot__S`. Produces the finite set of (sub, pc) pairs
    representing all execution paths through the program structure. -/
def denot [DecidableEq Sub] [DecidableEq PC]
    (isa : SymbolicISA Sub PC State) : CompTree Sub PC → Finset (Branch Sub PC)
  | .skip => {Branch.skip isa}
  | .assign σ => {⟨σ, isa.pc_true⟩}
  | .assert φ => {⟨isa.id_sub, φ⟩}
  | .seq t₁ t₂ => composeBranchFinsets isa (denot isa t₁) (denot isa t₂)
  | .choice t₁ t₂ => choiceBranchFinsets (denot isa t₁) (denot isa t₂)
  | .guardedChoice guard tThen tElse =>
      choiceBranchFinsets
        (composeBranchFinsets isa {⟨isa.id_sub, guard⟩} (denot isa tThen))
        (composeBranchFinsets isa {⟨isa.id_sub, isa.pc_not guard⟩} (denot isa tElse))
  | .boundedIter _body 0 => {Branch.skip isa}
  | .boundedIter body (n + 1) =>
      -- 0 iterations (skip) ∪ (1 iteration of body ; up to n more iterations)
      choiceBranchFinsets
        {Branch.skip isa}
        (composeBranchFinsets isa (denot isa body) (denot isa (.boundedIter body n)))

/-! ## Concrete Denotation -/

/-- Concrete denotation: CompTree → transition relation on states.
    ICTAC: `denot_fun_nondet`. -/
def treeBehavior (isa : SymbolicISA Sub PC State) :
    CompTree Sub PC → State → State → Prop
  | .skip => skipBehavior
  | .assign σ => assignBehavior isa σ
  | .assert φ => assertBehavior isa φ
  | .seq t₁ t₂ => seqBehavior (treeBehavior isa t₁) (treeBehavior isa t₂)
  | .choice t₁ t₂ => choiceBehavior (treeBehavior isa t₁) (treeBehavior isa t₂)
  | .guardedChoice guard tThen tElse =>
      choiceBehavior
        (seqBehavior (assertBehavior isa guard) (treeBehavior isa tThen))
        (seqBehavior (assertBehavior isa (isa.pc_not guard)) (treeBehavior isa tElse))
  | .boundedIter _body 0 => skipBehavior
  | .boundedIter body (n + 1) =>
      choiceBehavior skipBehavior
        (seqBehavior (treeBehavior isa body) (treeBehavior isa (.boundedIter body n)))

/-! ## Structural Bound -/

/-- A priori bound on the number of branches in `denot tree`.
    Computable from the tree structure alone — no symbolic execution needed. -/
def bound : CompTree Sub PC → Nat
  | .skip | .assign _ | .assert _ => 1
  | .seq t₁ t₂ => bound t₁ * bound t₂
  | .choice t₁ t₂ => bound t₁ + bound t₂
  | .guardedChoice _guard tThen tElse => bound tThen + bound tElse
  | .boundedIter _body 0 => 1
  | .boundedIter body (n + 1) => 1 + bound body * bound (.boundedIter body n)

/-! ## Core Theorem: Soundness and Completeness

The symbolic denotation `denot` is sound and complete w.r.t. the concrete
denotation `treeBehavior`, by structural induction on the CompTree.

We prove soundness and completeness separately, then combine. -/

section SoundComplete

variable [DecidableEq Sub] [DecidableEq PC] (isa : SymbolicISA Sub PC State)

/-- Soundness: `denot tree` is sound for `treeBehavior tree`.
    Every satisfiable branch in the symbolic denotation corresponds to a
    real transition in the concrete semantics.

    ICTAC: `SE_correct` (Theorem 2, forward direction). -/
theorem denot_sound (tree : CompTree Sub PC) :
    BranchModel.Sound isa (↑(denot isa tree) : Set (Branch Sub PC))
      (treeBehavior isa tree) := by
  induction tree with
  | skip =>
    simp only [denot, treeBehavior]
    rw [Finset.coe_singleton]
    exact skip_sound isa
  | assign σ =>
    simp only [denot, treeBehavior]
    rw [Finset.coe_singleton]
    exact assign_sound isa σ
  | assert φ =>
    simp only [denot, treeBehavior]
    rw [Finset.coe_singleton]
    exact assert_sound isa φ
  | seq t₁ t₂ ih₁ ih₂ =>
    simp only [denot, treeBehavior]
    rw [composeBranchFinsets_coe]
    exact composeBranchSets_sound isa ih₁ ih₂
  | choice t₁ t₂ ih₁ ih₂ =>
    simp only [denot, treeBehavior]
    rw [choiceBranchFinsets_coe]
    exact choiceBranchSets_sound isa ih₁ ih₂
  | guardedChoice guard tThen tElse ihThen ihElse =>
    simp only [denot, treeBehavior]
    rw [choiceBranchFinsets_coe]
    apply choiceBranchSets_sound isa
    · rw [composeBranchFinsets_coe]
      exact composeBranchSets_sound isa
        (by rw [Finset.coe_singleton]; exact assert_sound isa guard) ihThen
    · rw [composeBranchFinsets_coe]
      exact composeBranchSets_sound isa
        (by rw [Finset.coe_singleton]; exact assert_sound isa (isa.pc_not guard)) ihElse
  | boundedIter body n ih =>
    induction n with
    | zero =>
      simp only [denot, treeBehavior]
      rw [Finset.coe_singleton]
      exact skip_sound isa
    | succ n ihn =>
      simp only [denot, treeBehavior]
      rw [choiceBranchFinsets_coe]
      apply choiceBranchSets_sound isa
      · rw [Finset.coe_singleton]; exact skip_sound isa
      · rw [composeBranchFinsets_coe]
        exact composeBranchSets_sound isa ih ihn

/-- Completeness: `denot tree` is complete for `treeBehavior tree`.
    Every concrete transition is witnessed by some branch in the symbolic
    denotation.

    ICTAC: `SE_complete` (Theorem 2, backward direction). -/
theorem denot_complete (tree : CompTree Sub PC) :
    BranchModel.Complete isa (↑(denot isa tree) : Set (Branch Sub PC))
      (treeBehavior isa tree) := by
  induction tree with
  | skip =>
    simp only [denot, treeBehavior]
    rw [Finset.coe_singleton]
    exact skip_complete isa
  | assign σ =>
    simp only [denot, treeBehavior]
    rw [Finset.coe_singleton]
    exact assign_complete isa σ
  | assert φ =>
    simp only [denot, treeBehavior]
    rw [Finset.coe_singleton]
    exact assert_complete isa φ
  | seq t₁ t₂ ih₁ ih₂ =>
    simp only [denot, treeBehavior]
    rw [composeBranchFinsets_coe]
    exact composeBranchSets_complete isa ih₁ ih₂
  | choice t₁ t₂ ih₁ ih₂ =>
    simp only [denot, treeBehavior]
    rw [choiceBranchFinsets_coe]
    exact choiceBranchSets_complete isa ih₁ ih₂
  | guardedChoice guard tThen tElse ihThen ihElse =>
    simp only [denot, treeBehavior]
    rw [choiceBranchFinsets_coe]
    apply choiceBranchSets_complete isa
    · rw [composeBranchFinsets_coe]
      exact composeBranchSets_complete isa
        (by rw [Finset.coe_singleton]; exact assert_complete isa guard) ihThen
    · rw [composeBranchFinsets_coe]
      exact composeBranchSets_complete isa
        (by rw [Finset.coe_singleton]; exact assert_complete isa (isa.pc_not guard)) ihElse
  | boundedIter body n ih =>
    induction n with
    | zero =>
      simp only [denot, treeBehavior]
      rw [Finset.coe_singleton]
      exact skip_complete isa
    | succ n ihn =>
      simp only [denot, treeBehavior]
      rw [choiceBranchFinsets_coe]
      apply choiceBranchSets_complete isa
      · rw [Finset.coe_singleton]; exact skip_complete isa
      · rw [composeBranchFinsets_coe]
        exact composeBranchSets_complete isa ih ihn

/-- The core theorem: symbolic denotation is sound AND complete for the
    concrete semantics.

    ICTAC Theorem 2 (`SE_correct ∧ SE_complete`), generalized from ICTAC's
    concrete syntax to arbitrary CompTree over any SymbolicISA. -/
theorem denot_sound_complete (tree : CompTree Sub PC) :
    BranchModel.Sound isa (↑(denot isa tree) : Set (Branch Sub PC))
      (treeBehavior isa tree) ∧
    BranchModel.Complete isa (↑(denot isa tree) : Set (Branch Sub PC))
      (treeBehavior isa tree) :=
  ⟨denot_sound isa tree, denot_complete isa tree⟩

end SoundComplete

end CompTree
