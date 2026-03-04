import LTS

/-!
# Conditional Simulation

Conditional simulation: observing an LTS through a lossy projection and
using an oracle to reconstruct behavior. Defines Projection,
X-controllability, implementation-internal transitions, oracle
soundness/completeness, branching oracles, and the core simulation
theorems. The simulation is conditional on oracle properties — soundness
gives forward simulation, completeness gives reverse simulation.
-/

/-! ## Projection

The projection π : Σ → X maps the full host state to the program-relevant
configuration. X is the transitive closure of AST-bound state—everything
causally influenced by program structure.
-/

/-- The projection from host state to program-relevant configuration. -/
abbrev Projection (HostState Config : Type*) := HostState → Config

/-! ## X-Controllable and Implementation-Internal Transitions

A transition is **X-controllable** at state s when the projected state
π(s) is sufficient to determine its availability: any host state with
the same projection can also take that transition. These are the branches
that matter for the extracted LTS — they must appear in Alt(s).

A transition is **implementation-internal** when it doesn't change the
projected state. These are invisible to G' and don't need to be captured
by the branching oracle.
-/

/-- A label ℓ is X-controllable at state s: the projected state determines
    whether this transition fires. For any host state with the same
    projection, the transition via ℓ is also available. -/
abbrev IsXControllable {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (s : HostState) (ℓ : L) : Prop :=
  ∀ (σ : HostState), π σ = π s → ∃ (s' : HostState), H_I.step σ ℓ s'

/-- A transition s →ℓ s' is implementation-internal: it fires but doesn't
    change the projected state. Invisible to the extracted LTS. -/
abbrev IsImplementationInternal {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (s s' : HostState) (ℓ : L) : Prop :=
  H_I.step s ℓ s' ∧ π s = π s'

/-! ## Oracles: Value Transformation and Branching

The extraction relies on two oracles:

1. **Value-transformation oracle** (R): for each label ℓ, a relation
   R_ℓ(x, x') capturing the state transformation of the region.
   Soundness: every concrete step is captured. Completeness: R claims
   no transitions beyond what H_I exhibits.

2. **Branching oracle** (B): for each configuration x, the set of
   feasible labels B(x). Soundness: claimed labels are feasible.
   Completeness: all feasible labels are claimed.

**Dependency chain**: The simulation theorems below only require R to be
sound/complete—they don't mention B. However, *constructing* a sound R
requires complete branching discovery: if the branching oracle misses a
label ℓ, then R_ℓ will be wrong/absent, violating `OracleSoundFor`.
So branching oracle completeness is a prerequisite for value oracle
soundness, not a separate theorem hypothesis.

**B–R relationship**: The canonical B is the domain of R:
`B x ℓ := ∃ x', R ℓ x x'`. Under this definition,
`OracleSoundFor R` implies `BranchOracleCompleteFor B`, and
`OracleCompleteFor R` implies `BranchOracleSoundFor B`.
-/

/-- An oracle is sound for an LTS through a projection when every
    concrete step is captured by the corresponding relation on
    projected states. This subsumes branching oracle completeness:
    a sound value oracle induces a complete branching oracle
    (see `BranchOracleCompleteFor_of_OracleSoundFor`). -/
abbrev OracleSoundFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop) : Prop :=
  ∀ (σ σ' : HostState) (ℓ : L),
    H_I.Reachable σ → H_I.step σ ℓ σ' → R ℓ (π σ) (π σ')

/-- An oracle is complete for an LTS through a projection when every
    claimed transition is realizable from any concrete state projecting
    to the source. This captures that π contains all state relevant to
    transition behavior: non-projected state cannot block a transition
    that R claims is possible. This subsumes branching oracle soundness:
    a complete value oracle induces a sound branching oracle
    (see `BranchOracleSoundFor_of_OracleCompleteFor`). -/
abbrev OracleCompleteFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop) : Prop :=
  ∀ (σ : HostState) (x' : Config) (ℓ : L),
    R ℓ (π σ) x' → ∃ (σ' : HostState), H_I.step σ ℓ σ' ∧ π σ' = x'

/- **Paper correspondence only.** The following BranchingOracle definitions
   exist for correspondence with Section III-A of the paper. The extraction
   pipeline uses only `OracleSoundFor`/`OracleCompleteFor`; the subsumption
   theorems below show that a sound value oracle induces a complete branching
   oracle (and vice versa). -/

/-- A branching oracle: for each configuration, which labels are feasible. -/
abbrev BranchingOracle (Config L : Type*) := Config → L → Prop

/-- A branching oracle is sound when every claimed label is feasible
    from any concrete state projecting to that configuration. -/
abbrev BranchOracleSoundFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (B : BranchingOracle Config L) : Prop :=
  ∀ (σ : HostState) (ℓ : L),
    B (π σ) ℓ → ∃ (σ' : HostState), H_I.step σ ℓ σ'

/-- A branching oracle is complete when every feasible label is claimed. -/
abbrev BranchOracleCompleteFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (B : BranchingOracle Config L) : Prop :=
  ∀ (σ σ' : HostState) (ℓ : L),
    H_I.Reachable σ → H_I.step σ ℓ σ' → B (π σ) ℓ

/-- The canonical branching oracle induced by a value oracle:
    label ℓ is feasible from x iff R claims some transition. -/
abbrev BranchingOracle.ofValueOracle {Config : Type*} {L : Type*}
    (R : L → Config → Config → Prop) : BranchingOracle Config L :=
  fun x ℓ => ∃ x', R ℓ x x'

/-- A sound value oracle induces a complete branching oracle. -/
theorem BranchOracleCompleteFor_of_OracleSoundFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_sound : OracleSoundFor H_I π R) :
    BranchOracleCompleteFor H_I π (BranchingOracle.ofValueOracle R) :=
  fun σ σ' ℓ h_reach hstep => ⟨π σ', h_sound σ σ' ℓ h_reach hstep⟩

/-- A complete value oracle induces a sound branching oracle. -/
theorem BranchOracleSoundFor_of_OracleCompleteFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_complete : OracleCompleteFor H_I π R) :
    BranchOracleSoundFor H_I π (BranchingOracle.ofValueOracle R) := by
  intro σ ℓ ⟨x', hR⟩
  obtain ⟨σ', hstep, _⟩ := h_complete σ x' ℓ hR
  exact ⟨σ', hstep⟩

/-! ## Oracle-Induced Simulation and Bisimulation

Given a sound oracle R, the oracle LTS simulates H_I (forward simulation).
Given a complete oracle R, H_I simulates the oracle LTS (reverse simulation).
Together, soundness + completeness give bisimulation. The non-trivial content
lies in *establishing* these oracle properties (extraction pipeline,
co-refinement fixpoint), not in these implications themselves.
-/

/-- The LTS over configurations induced by an oracle: transitions are
    exactly the oracle's relational summaries. -/
def LTS.ofOracle {Config : Type*} {L : Type*}
    (init : Config) (R : L → Config → Config → Prop) : LTS Config L where
  init := init
  step := fun x ℓ x' => R ℓ x x'

/-- A sound oracle induces a forward simulation: the oracle LTS
    simulates H_I over reachable states via
    `fun x σ => π σ = x ∧ H_I.Reachable σ`. -/
theorem simulation_of_sound_oracle {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_sound : OracleSoundFor H_I π R) :
    (LTS.ofOracle (π H_I.init) R).Simulates H_I
      (fun x σ => π σ = x ∧ H_I.Reachable σ) where
  init := ⟨rfl, Relation.ReflTransGen.refl⟩
  step_match := by
    intro x σ ℓ σ' ⟨hrel, hreach⟩ hstep
    subst hrel
    exact ⟨π σ', h_sound σ σ' ℓ hreach hstep, rfl, hreach.step hstep⟩

/-- A complete oracle induces a reverse simulation: H_I simulates
    the oracle LTS via `fun σ x => π σ = x`. -/
theorem simulation_of_complete_oracle {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_complete : OracleCompleteFor H_I π R) :
    H_I.Simulates (LTS.ofOracle (π H_I.init) R) (fun σ x => π σ = x) where
  init := rfl
  step_match := by
    intro σ x ℓ x' hrel hstep
    subst hrel
    obtain ⟨σ', hstep', hproj⟩ := h_complete σ x' ℓ hstep
    exact ⟨σ', hstep', hproj⟩
