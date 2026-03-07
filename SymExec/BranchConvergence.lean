import Core.Branch
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Branch Accumulation and OGIS Convergence

Convergence of iterative branch accumulation from a symbolic execution oracle.

This replaces the dimension-refinement convergence in `Convergence.lean` with a
simpler model: the oracle produces branches (Sub × PC pairs), we accumulate them
into a finite set, and monotone growth bounded by a finite target set guarantees
stabilization.

## OGIS Mapping

This is Jha-Seshia's OGIS (Oracle-Guided Inductive Synthesis) instantiated with
ICTAC branch structure:

| OGIS concept | Our instantiation |
|---|---|
| Concept class | Possible branch models (sets of branches) |
| Target concept | Complete set of branches for the system |
| Oracle (q_ce) | Symbolic execution: given current model, produce a missing branch |
| Hypothesis | Current branch model (accumulated so far) |
| Convergence | Monotone accumulation bounded by finite target |

Our bound is |target| (not 2^|target|) because we do monotone accumulation,
not arbitrary hypothesis revision. Every oracle query adds exactly one branch.
Teaching dimension ≤ |target| (trivially; every branch is independently necessary).

## Architecture

The convergence argument is purely combinatorial:
1. Oracle produces sound branches not already in the model
2. Model grows monotonically (we only add, never remove)
3. Model is bounded by the target (oracle only produces target branches)
4. Monotone growth of a finite set bounded above → stabilizes
5. At stabilization: model = target (otherwise oracle would produce more)

Minimal classical reasoning (`by_contra` for existence proofs). No `Fintype` on the branch types — finiteness is
a hypothesis on the specific system ("this program has finitely many branches"),
not a constraint on the types.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Bounded Monotone Stabilization

A monotone increasing sequence of finsets bounded by a fixed finset must
eventually stabilize. Unlike `Finset.monotone_stabilizes` in Convergence.lean,
this does NOT require `Fintype α` — just a bounding finset. -/

/-- A monotone increasing sequence of finsets bounded above by a fixed finset
    must stabilize: there exists `n` with `s n = s (n + 1)`.

    Proof: cardinality is non-decreasing and bounded by `bound.card`.
    If it never stabilizes, cardinality strictly increases at every step,
    giving `n ≤ (s n).card` for all n. At `n = bound.card + 1` this
    contradicts the bound. -/
theorem Finset.bounded_monotone_stabilizes {α : Type*}
    (s : ℕ → Finset α) (bound : Finset α)
    (h_mono : ∀ n, s n ⊆ s (n + 1))
    (h_bound : ∀ n, s n ⊆ bound) :
    ∃ n, s n = s (n + 1) := by
  by_contra h_all_ne
  push_neg at h_all_ne
  have h_ssubset : ∀ n, s n ⊂ s (n + 1) :=
    fun n => (h_mono n).ssubset_of_ne (h_all_ne n)
  have h_card_lt : ∀ n, (s n).card < (s (n + 1)).card :=
    fun n => Finset.card_lt_card (h_ssubset n)
  have h_lower : ∀ n, n ≤ (s n).card := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (h_card_lt n))
  have h_upper := Finset.card_le_card (h_bound (bound.card + 1))
  exact absurd (Nat.le_trans (h_lower (bound.card + 1)) h_upper) (by omega)

/-- Explicit bound: stabilization occurs within `bound.card` steps. -/
theorem Finset.bounded_monotone_stabilizes_within {α : Type*}
    (s : ℕ → Finset α) (bound : Finset α)
    (h_mono : ∀ n, s n ⊆ s (n + 1))
    (h_bound : ∀ n, s n ⊆ bound) :
    ∃ n, n ≤ bound.card ∧ s n = s (n + 1) := by
  by_contra h_none
  push_neg at h_none
  have h_ssubset : ∀ n, n ≤ bound.card → s n ⊂ s (n + 1) :=
    fun n hn => (h_mono n).ssubset_of_ne (h_none n hn)
  have h_card_lt : ∀ n, n ≤ bound.card → (s n).card < (s (n + 1)).card :=
    fun n hn => Finset.card_lt_card (h_ssubset n hn)
  have h_lower : ∀ n, n ≤ bound.card → n ≤ (s n).card := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have hn' : n ≤ bound.card := Nat.le_of_succ_le hn
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih hn') (h_card_lt n hn'))
  have h_bc := h_lower bound.card (Nat.le_refl _)
  have h_ub := Finset.card_le_card (h_bound bound.card)
  have h_lt := h_card_lt bound.card (Nat.le_refl _)
  have h_ub2 := Finset.card_le_card (h_bound (bound.card + 1))
  omega


/-! ## Branch Oracle

A `BranchOracle` models what symbolic execution provides: given the current
branch model, it either produces a new sound branch not already in the model,
or returns `none` (indicating it has nothing more to offer).

The oracle bundles the ISA and behavior it's sound with respect to. -/

/-- A branch oracle: queries a symbolic executor for branches.

    Given the current model (as a `Finset`), the oracle either produces a
    new branch or returns `none`. When it produces a branch, that branch
    is sound w.r.t. the real behavior and not already in the model. -/
structure BranchOracle (Sub PC State : Type*) [DecidableEq Sub] [DecidableEq PC] where
  /-- The ISA this oracle operates over. -/
  isa : SymbolicISA Sub PC State
  /-- The real system behavior. -/
  behavior : State → State → Prop
  /-- Query the oracle: given current model, maybe produce a new branch. -/
  query : Finset (Branch Sub PC) → Option (Branch Sub PC)
  /-- Any returned branch is sound: satisfying its PC yields real behavior. -/
  query_sound : ∀ (model : Finset (Branch Sub PC)) (b : Branch Sub PC),
    query model = some b →
    ∀ (s : State), isa.satisfies s b.pc → behavior s (isa.eval_sub b.sub s)
  /-- Any returned branch is new: not already in the model. -/
  query_new : ∀ (model : Finset (Branch Sub PC)) (b : Branch Sub PC),
    query model = some b → b ∉ model


/-! ## Oracle Step and Sequence

`oracleStep` advances the model by one oracle query: if the oracle returns
a branch, insert it; otherwise keep the model unchanged.

`oracleSequence` iterates from the empty set. -/

section OracleIteration

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]

/-- One step of oracle-guided accumulation: query the oracle, insert result
    if it returns one, otherwise no-op. -/
def oracleStep (oracle : BranchOracle Sub PC State)
    (model : Finset (Branch Sub PC)) : Finset (Branch Sub PC) :=
  match oracle.query model with
  | some b => insert b model
  | none   => model

/-- The oracle sequence: iterate `oracleStep` from the empty set. -/
def oracleSequence (oracle : BranchOracle Sub PC State) (n : ℕ) :
    Finset (Branch Sub PC) :=
  (oracleStep oracle)^[n] ∅

end OracleIteration


/-! ## Refinement Invariants

The oracle step is monotone (model only grows) and preserves soundness. -/

section Invariants

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]

/-- `oracleStep` produces a superset of the input. -/
theorem oracleStep_mono (oracle : BranchOracle Sub PC State)
    (model : Finset (Branch Sub PC)) :
    model ⊆ oracleStep oracle model := by
  unfold oracleStep
  cases hq : oracle.query model with
  | none => exact Finset.Subset.refl model
  | some b => exact Finset.subset_insert b model

/-- The oracle sequence is monotone. -/
theorem oracleSequence_mono (oracle : BranchOracle Sub PC State) :
    ∀ n, oracleSequence oracle n ⊆ oracleSequence oracle (n + 1) := by
  intro n
  show (oracleStep oracle)^[n] ∅ ⊆ (oracleStep oracle)^[n + 1] ∅
  rw [Function.iterate_succ_apply']
  exact oracleStep_mono oracle _

/-- Soundness of oracleStep: if the input model is sound, so is the output. -/
theorem oracleStep_sound (oracle : BranchOracle Sub PC State)
    (model : Finset (Branch Sub PC))
    (h_sound : BranchModel.Sound oracle.isa (↑model : Set (Branch Sub PC)) oracle.behavior) :
    BranchModel.Sound oracle.isa (↑(oracleStep oracle model) : Set (Branch Sub PC)) oracle.behavior := by
  unfold oracleStep
  cases hq : oracle.query model with
  | none => exact h_sound
  | some b =>
    rw [Finset.coe_insert]
    exact BranchModel.Sound.insert oracle.isa h_sound (oracle.query_sound _ b hq)

/-- Soundness is preserved through the oracle sequence. -/
theorem oracleSequence_sound (oracle : BranchOracle Sub PC State) :
    ∀ n, BranchModel.Sound oracle.isa
      (↑(oracleSequence oracle n) : Set (Branch Sub PC)) oracle.behavior := by
  intro n
  induction n with
  | zero =>
    show BranchModel.Sound oracle.isa (↑(∅ : Finset (Branch Sub PC))) oracle.behavior
    rw [Finset.coe_empty]
    exact BranchModel.Sound.empty oracle.isa oracle.behavior
  | succ n ih =>
    show BranchModel.Sound oracle.isa
      (↑((oracleStep oracle)^[n + 1] ∅) : Set (Branch Sub PC)) oracle.behavior
    rw [Function.iterate_succ_apply']
    exact oracleStep_sound oracle _ ih

end Invariants


/-! ## Productivity and Convergence

A **productive** oracle always returns a branch when the model is incomplete
(a strict subset of some target). A **target-bounded** oracle only returns
branches from the target. Together: productive + bounded → the model reaches
the target in at most |target| steps. -/

section Convergence

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]

/-- An oracle is productive w.r.t. a target: if the model is a strict subset
    of the target, the oracle returns something. -/
def BranchOracle.Productive (oracle : BranchOracle Sub PC State)
    (target : Finset (Branch Sub PC)) : Prop :=
  ∀ (model : Finset (Branch Sub PC)),
    model ⊆ target → model ≠ target →
    ∃ b, oracle.query model = some b

/-- An oracle is target-bounded: it only returns branches from the target. -/
def BranchOracle.TargetBounded (oracle : BranchOracle Sub PC State)
    (target : Finset (Branch Sub PC)) : Prop :=
  ∀ (model : Finset (Branch Sub PC)) (b : Branch Sub PC),
    oracle.query model = some b → b ∈ target

/-- When the oracle is target-bounded, `oracleStep` preserves the bound. -/
theorem oracleStep_bounded (oracle : BranchOracle Sub PC State)
    (target : Finset (Branch Sub PC))
    (h_bounded : oracle.TargetBounded target)
    (model : Finset (Branch Sub PC))
    (h_sub : model ⊆ target) :
    oracleStep oracle model ⊆ target := by
  intro x hx
  -- Either x was already in model, or x is the newly inserted branch
  by_cases hxm : x ∈ model
  · exact h_sub hxm
  · -- x is new: it must be the branch the oracle returned
    unfold oracleStep at hx
    revert hx
    cases hq : oracle.query model with
    | none => intro hx; exact absurd hx hxm
    | some _ =>
      intro hx
      have := Finset.mem_insert.mp hx
      rcases this with rfl | hx'
      · exact h_bounded model _ hq
      · exact absurd hx' hxm

/-- The oracle sequence stays bounded by the target. -/
theorem oracleSequence_bounded (oracle : BranchOracle Sub PC State)
    (target : Finset (Branch Sub PC))
    (h_bounded : oracle.TargetBounded target) :
    ∀ n, oracleSequence oracle n ⊆ target := by
  intro n
  induction n with
  | zero => exact Finset.empty_subset target
  | succ n ih =>
    show (oracleStep oracle)^[n + 1] ∅ ⊆ target
    rw [Function.iterate_succ_apply']
    exact oracleStep_bounded oracle target h_bounded _ ih

/-- Main convergence theorem: a target-bounded oracle drives the model to
    stabilization within |target| steps. -/
theorem branchAccumulation_stabilizes (oracle : BranchOracle Sub PC State)
    (target : Finset (Branch Sub PC))
    (h_bounded : oracle.TargetBounded target) :
    ∃ n, n ≤ target.card ∧
      oracleSequence oracle n = oracleSequence oracle (n + 1) :=
  Finset.bounded_monotone_stabilizes_within
    (oracleSequence oracle) target
    (oracleSequence_mono oracle)
    (oracleSequence_bounded oracle target h_bounded)

/-- At stabilization with a productive oracle, the model equals the target.

    Proof by contradiction: if model ≠ target but model ⊆ target, productivity
    gives a branch b. Then oracleStep inserts b (b ∉ model from query_new),
    so oracleSequence grows — contradicting stabilization. -/
theorem branchAccumulation_complete_at_fixpoint
    (oracle : BranchOracle Sub PC State)
    (target : Finset (Branch Sub PC))
    (h_productive : oracle.Productive target)
    (h_bounded : oracle.TargetBounded target)
    {n : ℕ}
    (h_fix : oracleSequence oracle n = oracleSequence oracle (n + 1)) :
    oracleSequence oracle n = target := by
  by_contra h_ne
  have h_sub := oracleSequence_bounded oracle target h_bounded n
  obtain ⟨b, hq⟩ := h_productive (oracleSequence oracle n) h_sub h_ne
  -- b ∉ model (from query_new)
  have h_not_mem := oracle.query_new _ b hq
  -- But oracleStep inserts b, making model grow
  have h_mem : b ∈ oracleStep oracle (oracleSequence oracle n) := by
    unfold oracleStep
    simp [hq, Finset.mem_insert]
  -- oracleSequence (n + 1) = oracleStep oracle (oracleSequence oracle n)
  have h_eq : oracleSequence oracle (n + 1) =
      oracleStep oracle (oracleSequence oracle n) := by
    show (oracleStep oracle)^[n + 1] ∅ = _
    rw [Function.iterate_succ_apply']; rfl
  -- So b ∈ oracleSequence (n + 1)
  have h_mem2 : b ∈ oracleSequence oracle (n + 1) := h_eq ▸ h_mem
  -- But h_fix says oracleSequence n = oracleSequence (n + 1)
  rw [← h_fix] at h_mem2
  exact h_not_mem h_mem2

end Convergence


/-! ## End-to-End Theorem

Combining soundness, convergence, and completeness at fixpoint:
a productive, target-bounded oracle with a sound and complete target
produces a sound and complete model in at most |target| steps. -/

section EndToEnd

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]

/-- End-to-end: productive + target-bounded oracle → sound and complete model.

    Given:
    - An oracle that is productive and target-bounded
    - A target that is complete w.r.t. real behavior

    Then: there exists n ≤ |target| such that the oracle sequence at n
    is both sound and complete.

    This IS OGIS convergence for the branch framework. The bound |target|
    corresponds to the number of execution paths — for bounded-input programs,
    this is finite and often small. -/
theorem branchAccumulation_sound_and_complete
    (oracle : BranchOracle Sub PC State)
    (target : Finset (Branch Sub PC))
    (h_productive : oracle.Productive target)
    (h_bounded : oracle.TargetBounded target)
    (h_target_complete : BranchModel.Complete oracle.isa
      (↑target : Set (Branch Sub PC)) oracle.behavior) :
    ∃ n, n ≤ target.card ∧
      BranchModel.Sound oracle.isa
        (↑(oracleSequence oracle n) : Set (Branch Sub PC)) oracle.behavior ∧
      BranchModel.Complete oracle.isa
        (↑(oracleSequence oracle n) : Set (Branch Sub PC)) oracle.behavior := by
  obtain ⟨n, h_le, h_fix⟩ := branchAccumulation_stabilizes oracle target h_bounded
  refine ⟨n, h_le, oracleSequence_sound oracle n, ?_⟩
  have h_eq := branchAccumulation_complete_at_fixpoint oracle target h_productive h_bounded h_fix
  rw [h_eq]
  exact h_target_complete

end EndToEnd
