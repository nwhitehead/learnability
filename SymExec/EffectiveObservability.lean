import SymExec.ProgramStructure
import SymExec.Quotient

/-!
# Operational Oracle — Symbolic Execution as BranchOracle

The oracle IS symbolic execution: given a CompTree and the current branch model,
it finds a branch in `denot tree` not yet in the model. This connects CompTree
(program structure) to the oracle-guided convergence machinery from Phase 2.

## Architecture

We do NOT implement a step-by-step symbolic executor (that would duplicate
`denot`). Instead, we directly construct a `BranchOracle` from `denot tree`
using the fact that `denot tree` is a `Finset` and we can enumerate it.

The key insight: since `denot_sound_complete` proves that `denot tree` IS the
complete set of branches, we can use `denot tree` itself as the target for
oracle convergence. The oracle just picks the first branch in `denot tree`
that's not yet in the model.

## End-to-End Theorem

```
programConverges : ∃ n, n ≤ bound tree ∧ Bisimilar ...
```

The convergence bound is `bound tree` — a program-structural quantity
computable BEFORE running symbolic execution.

## ICTAC Correspondence

| EffectiveObservability.lean | ICTAC |
|---|---|
| `treeOracle` | operational semantics (Theorems 3+4) |
| `programConverges` | end-to-end correctness |
| `bound tree` | structural bound on execution paths |
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Oracle from Finset

Given a target `Finset`, build an oracle that enumerates branches from it.
The query uses decidable membership to find a target branch not yet in the model. -/

section FinsetOracle

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]

/-- Pick a branch from `target \ model` if the difference is nonempty.
    Uses `Decidable` on `target \ model = ∅`. -/
noncomputable def finsetQuery (target : Finset (Branch Sub PC))
    (model : Finset (Branch Sub PC)) : Option (Branch Sub PC) :=
  if h : (target \ model).Nonempty then some h.choose else none

/-- The chosen element is in the sdiff. -/
private theorem finsetQuery_choose_mem (target model : Finset (Branch Sub PC))
    (h : (target \ model).Nonempty) :
    h.choose ∈ target \ model :=
  h.choose_spec

/-- The query returns elements from the target. -/
theorem finsetQuery_mem_target (target model : Finset (Branch Sub PC))
    (b : Branch Sub PC) (hq : finsetQuery target model = some b) :
    b ∈ target := by
  simp only [finsetQuery] at hq
  split at hq
  case isTrue h =>
    have := Option.some_injective _ hq
    rw [← this]
    exact (Finset.mem_sdiff.mp (finsetQuery_choose_mem target model h)).1
  case isFalse => simp at hq

/-- The query returns elements not in the model. -/
theorem finsetQuery_not_mem (target model : Finset (Branch Sub PC))
    (b : Branch Sub PC) (hq : finsetQuery target model = some b) :
    b ∉ model := by
  simp only [finsetQuery] at hq
  split at hq
  case isTrue h =>
    have := Option.some_injective _ hq
    rw [← this]
    exact (Finset.mem_sdiff.mp (finsetQuery_choose_mem target model h)).2
  case isFalse => simp at hq

/-- The query is productive: if model ⊊ target, it returns something. -/
theorem finsetQuery_productive (target model : Finset (Branch Sub PC))
    (h_sub : model ⊆ target) (h_ne : model ≠ target) :
    ∃ b, finsetQuery target model = some b := by
  have h_nonempty : (target \ model).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro h_sub'
    exact h_ne (Finset.Subset.antisymm h_sub h_sub')
  simp only [finsetQuery, h_nonempty, dite_true]
  exact ⟨_, rfl⟩

/-- Build a BranchOracle from a target Finset, an ISA, and a behavior.
    The oracle is sound if every branch in the target is sound. -/
noncomputable def finsetOracle (isa : SymbolicISA Sub PC State)
    (behavior : State → State → Prop)
    (target : Finset (Branch Sub PC))
    (h_target_sound : BranchModel.Sound isa (↑target : Set (Branch Sub PC)) behavior) :
    BranchOracle Sub PC State where
  isa := isa
  behavior := behavior
  query := finsetQuery target
  query_sound := by
    intro model b hq s hsat
    have hmem := finsetQuery_mem_target target model b hq
    exact h_target_sound b (Finset.mem_coe.mpr hmem) s hsat
  query_new := fun model b hq => finsetQuery_not_mem target model b hq

/-- The finsetOracle is productive w.r.t. its target. -/
theorem finsetOracle_productive (isa : SymbolicISA Sub PC State)
    (behavior : State → State → Prop)
    (target : Finset (Branch Sub PC))
    (h_sound : BranchModel.Sound isa (↑target) behavior) :
    (finsetOracle isa behavior target h_sound).Productive target :=
  fun model h_sub h_ne => finsetQuery_productive target model h_sub h_ne

/-- The finsetOracle is target-bounded. -/
theorem finsetOracle_bounded (isa : SymbolicISA Sub PC State)
    (behavior : State → State → Prop)
    (target : Finset (Branch Sub PC))
    (h_sound : BranchModel.Sound isa (↑target) behavior) :
    (finsetOracle isa behavior target h_sound).TargetBounded target :=
  fun model b hq => finsetQuery_mem_target target model b hq

end FinsetOracle


/-! ## Tree Oracle

The oracle for a CompTree: enumerate branches from `denot tree`. -/

section TreeOracle

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]

/-- Build a BranchOracle from a CompTree.
    Uses `denot tree` as the target set. Sound because `denot_sound`. -/
noncomputable def treeOracle (isa : SymbolicISA Sub PC State)
    (tree : CompTree Sub PC) :
    BranchOracle Sub PC State :=
  finsetOracle isa (CompTree.treeBehavior isa tree) (CompTree.denot isa tree)
    (CompTree.denot_sound isa tree)

/-- The tree oracle is productive w.r.t. `denot tree`. -/
theorem treeOracle_productive (isa : SymbolicISA Sub PC State)
    (tree : CompTree Sub PC) :
    (treeOracle isa tree).Productive (CompTree.denot isa tree) :=
  finsetOracle_productive isa _ _ _

/-- The tree oracle is target-bounded w.r.t. `denot tree`. -/
theorem treeOracle_bounded (isa : SymbolicISA Sub PC State)
    (tree : CompTree Sub PC) :
    (treeOracle isa tree).TargetBounded (CompTree.denot isa tree) :=
  finsetOracle_bounded isa _ _ _

end TreeOracle


/-! ## End-to-End: Program Convergence

The convergence bound is `(denot tree).card` — bounded by `bound tree`. -/

section EndToEnd

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]

/-- End-to-end: symbolic execution of a CompTree converges to a bisimilar
    model in at most `(denot tree).card` steps.

    This connects:
    - Phase 7: `denot tree` is sound ∧ complete for `treeBehavior tree`
    - Phase 2: oracle-guided accumulation converges
    - Phase 3: at convergence, the model is bisimilar to the real system -/
theorem programConverges_bisimilar (isa : SymbolicISA Sub PC State)
    (tree : CompTree Sub PC) :
    ∃ n, n ≤ (CompTree.denot isa tree).card ∧
      Bisimilar
        (branchBehavior isa
          (↑(oracleSequence (treeOracle isa tree) n) : Set (Branch Sub PC)))
        (CompTree.treeBehavior isa tree) :=
  branchAccumulation_bisimilar
    (treeOracle isa tree) (CompTree.denot isa tree)
    (treeOracle_productive isa tree)
    (treeOracle_bounded isa tree)
    (CompTree.denot_complete isa tree)

/-- End-to-end with quotient: if the ISA has decidable satisfaction and
    PC is finite, we also get a cross-system bisimulation via the quotient.
    (MachineISA's MBool is NOT Fintype, so this applies to finite-PC ISAs
    like BranchExample, not to MachineISA.) -/
theorem programConverges_quotient (isa : SymbolicISA Sub PC State)
    (tree : CompTree Sub PC)
    [Fintype PC]
    [∀ (s : State) (φ : PC), Decidable (isa.satisfies s φ)] :
    ∃ n, n ≤ (CompTree.denot isa tree).card ∧
      Bisimilar
        (branchBehavior isa
          (↑(oracleSequence (treeOracle isa tree) n) : Set (Branch Sub PC)))
        (CompTree.treeBehavior isa tree) ∧
      CrossBisimulation
        (Quotient.mk (pcSetoid isa (oracleSequence (treeOracle isa tree) n)))
        (CompTree.treeBehavior isa tree)
        (abstractBehavior isa (oracleSequence (treeOracle isa tree) n)) := by
  obtain ⟨n, h_le, h_bisim⟩ := programConverges_bisimilar isa tree
  refine ⟨n, h_le, h_bisim, ?_⟩
  obtain ⟨h_sound, h_complete⟩ := (sound_complete_iff_bisimilar isa _ _).mpr h_bisim
  exact quotient_bisimulation isa (oracleSequence (treeOracle isa tree) n)
    (CompTree.treeBehavior isa tree) h_sound h_complete

end EndToEnd
