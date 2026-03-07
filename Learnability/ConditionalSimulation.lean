import Core.LTS

/-!
# Conditional Simulation

The theoretical core of the extraction technique: characterizing when a
projection of an implementation LTS faithfully captures guest-language
operational semantics.

## The setup: guest/host language extraction

The host system `H_I` evaluates programs in a guest language. `HostState`
contains everything the host needs — stack frames, allocator metadata, OS
resources, implementation bookkeeping. `Config` is the guest-language
operational state — everything the *guest* program cares about. The projection
`π : HostState → Config` recovers guest-level state from host evaluation state.

This is not lossy observation. It is **semantic recovery**: `π` identifies the
guest-level structure the host is computing over. When `π` is correctly chosen,
the oracle `R : L → Config → Config → Prop` captures the guest language's
transition relation exactly — R *is* the extracted operational semantics.

## The Galois connection: the central organizing idea

A Galois connection is a pair of maps (α, γ) between two ordered sets forming a
"best approximation" relationship: α(x) ≤ y if and only if x ≤ γ(y). Here the
orders are set inclusion on step relations, and the maps are induced by π.

`π` induces two natural maps on step relations:

- **α(S)** `= {(π σ, ℓ, π σ') | (σ, ℓ, σ') ∈ S}` — abstraction: image under π
- **γ(R)** `= {(σ, ℓ, σ') | (π σ, ℓ, π σ') ∈ R}` — concretization: preimage under π

These form a Galois connection: `α(S) ⊆ R ↔ S ⊆ γ(R)`.

The oracle conditions are the two halves:

- **`OracleSoundFor`** = `α(H_I.step) ⊆ R`: every concrete step from a
  *reachable* state, when projected via π, appears in R. The oracle contains
  the full abstraction of the implementation's reachable behavior.

- **`OracleRealizableFor`** = `R ⊆ α(H_I.step)`: every oracle claim is
  witnessed by *some* concrete step (no reachability guard). The oracle claims
  nothing the implementation doesn't do.

- **Together**: `R = α(H_I.step)` over reachable states. **R is exactly the
  guest-level semantics** — the precise image of the host's reachable
  transitions under π.

Note the deliberate asymmetry: soundness is restricted to reachable states
(unreachable behavior is irrelevant to simulation), while realizability is
unrestricted (any oracle claim must be concretely witnessed, regardless of
whether the witness is reachable). The bridge lemma
`oracleComplete_of_realizable_uniform` shows that `OracleRealizableFor +
ProjectionUniform` together recover the fused completeness condition.

## ProjectionUniform: making π a semantic quotient map

The Galois connection tells you what R should be. For the **reverse simulation**,
you need more: given oracle claim `R ℓ x x'` and a specific concrete state `σ`
with `π σ = x`, you need `σ` *itself* to be able to take the step — not just
some other state sharing σ's projection.

`ProjectionUniform` is the condition that licences this transfer. It says that
the hidden state — the part `π` discards — cannot affect (1) whether a
transition is available, or (2) what projected state it leads to. Formally: if
any host state with projection `x` can take `ℓ` to a state projecting to `x'`,
then **every** host state with projection `x` can do so.

This makes `π` a **semantic quotient map**: the guest-level transition relation
is well-defined on `π`-equivalence classes. Two host states indistinguishable
to the guest behave identically from the guest's perspective.

`ProjectionUniform` is a property of `H_I + π` only, independent of R. It is
what the co-refinement process (`Convergence.lean`) iteratively establishes:
each dimension added to X corrects a pair of states with the same current
projection that violate uniformity. At the fixpoint, no violation remains.

## Relation to IsXControllable

These two definitions capture the same intuition at different strengths —
both ask "does the projected state determine what happens?" but they differ
in what "what happens" means:

`IsXControllable` at `(s, ℓ)` says all `π`-equivalent states can take `ℓ`
(to *some* target, unconstrained). `ProjectionUniform` is the global, stronger
version: all `π`-equivalent states agree on the full `(ℓ, x')` transition set,
not just on label availability. At the co-refinement fixpoint, non-controllable
transitions are implementation-internal — they fire without changing the projected
state (`Convergence.lean`, `IsCoRefinementFixpoint.non_controllable_internal`).

## Why simulation is "conditional"

The implications here are almost immediate given the oracle conditions:
- `OracleSoundFor` → forward simulation: one line. Apply soundness to produce
  the oracle step from any concrete step.
- `OracleRealizableFor + ProjectionUniform` → reverse simulation: three lines.
  Realizability witnesses some concrete step; uniformity transfers it to the
  specific concrete state at hand.

The simulation is **conditional** because establishing these oracle properties
is the hard part. That is the job of the extraction pipeline and the
co-refinement process in `Convergence.lean`. The implications here are
theoretically thin; the weight is in earning the preconditions.

## What this file does NOT do

No dimension refinement, no iterative process, no convergence argument. This
file says: *given* that oracle conditions hold, these simulation results follow.
How to achieve those conditions is `Convergence.lean`.
-/

/-! ## Projection

`π : HostState → Config` recovers the guest-language operational state from
the host evaluation state. Host states in the same `π`-equivalence class
represent the same guest-language configuration — they differ only in
implementation detail that the guest language cannot observe.

The choice of `π` determines what counts as "the same" at the guest level.
Choosing it correctly — so that `ProjectionUniform` holds — is the content
of the extraction technique. The co-refinement process discovers the minimal
`π` for which uniformity holds.
-/

/-- The projection from host state to program-relevant configuration. -/
abbrev Projection (HostState Config : Type*) := HostState → Config

/-! ## X-Controllable and Implementation-Internal Transitions

"X" refers to the tracked dimension set — the subset of host-state dimensions
that the current extraction step considers relevant. In `Convergence.lean`,
X grows iteratively until it stabilizes; in `Learnability.lean`, it is the
`Finset Dim` at which `refineStep` reaches a fixpoint.

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

The oracle `R : L → Config → Config → Prop` summarizes the implementation's
transition behavior at the guest level. `R ℓ x x'` means: from guest state
`x`, the implementation can take label `ℓ` to arrive at guest state `x'`.
When `R = α(H_I.step)` — i.e., when both soundness and realizability hold —
R is exactly the guest language's operational semantics.

A separate **branching oracle** `B : Config → L → Prop` records which labels
are available from each configuration. `B x ℓ` means label `ℓ` is feasible
from `x`. The canonical choice is `B := domain(R)`: `B x ℓ := ∃ x', R ℓ x x'`.

**Dependency chain**: The simulation theorems below take R as hypothesis —
they don't mention B explicitly. However, *constructing* a sound R requires
discovering all branches first: if B misses a label ℓ, R will never have an
entry for it, violating `OracleSoundFor`. So branching oracle completeness is
a construction-time prerequisite for value oracle soundness, even though it
is logically a *consequence* of soundness (see `BranchOracleCompleteFor_of_OracleSoundFor`).

**B–R subsumption** (under the canonical `B = domain(R)`):
- `OracleSoundFor R` → `BranchOracleCompleteFor B`: soundness witnesses every
  branch, so B misses nothing.
- `OracleRealizableFor R + ProjectionUniform` → `BranchOracleSoundFor B`:
  every claimed branch is realizable from any concrete state with that projection.
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

/-- The Galois dual of OracleSoundFor: R ⊆ α(steps). Every claimed
    oracle transition is witnessed by at least one concrete step pair.
    Formally: OracleSoundFor says α(H_I.step) ⊆ R; this says R ⊆ α(H_I.step),
    where α maps via π image. Together they give R = α(H_I.step). -/
abbrev OracleRealizableFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop) : Prop :=
  ∀ (x x' : Config) (ℓ : L),
    R ℓ x x' → ∃ (σ σ' : HostState), π σ = x ∧ H_I.step σ ℓ σ' ∧ π σ' = x'

/-- Transition availability and projected target are determined by projected
    state alone: any two concrete states with the same projection agree on
    which transitions are available and where they lead (in projected space).
    This is a property of H_I and π independent of any particular oracle R.
    Together with OracleRealizableFor it gives the reverse simulation. -/
abbrev ProjectionUniform {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config) : Prop :=
  ∀ (σ₁ σ₂ : HostState) (ℓ : L) (x' : Config),
    π σ₁ = π σ₂ →
    (∃ σ₁', H_I.step σ₁ ℓ σ₁' ∧ π σ₁' = x') →
    (∃ σ₂', H_I.step σ₂ ℓ σ₂' ∧ π σ₂' = x')

/-- Bridge: OracleRealizableFor + ProjectionUniform recover the fused
    completeness condition. Every oracle claim is realizable from any
    concrete state with the matching projection. Documents that the split
    is lossless — the two components together are equivalent to the original
    fused `OracleCompleteFor`. -/
theorem oracleComplete_of_realizable_uniform {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_realizable : OracleRealizableFor H_I π R)
    (h_uniform : ProjectionUniform H_I π) :
    ∀ (σ : HostState) (x' : Config) (ℓ : L),
      R ℓ (π σ) x' → ∃ (σ' : HostState), H_I.step σ ℓ σ' ∧ π σ' = x' := by
  intro σ x' ℓ hR
  obtain ⟨σ₀, σ₀', hπ₀, hstep₀, hπ₀'⟩ := h_realizable _ _ _ hR
  exact h_uniform σ₀ σ ℓ x' hπ₀ ⟨σ₀', hstep₀, hπ₀'⟩

/- **Paper correspondence only.** The following BranchingOracle definitions
   exist for correspondence with Section III-A of the paper. The extraction
   pipeline uses only `OracleSoundFor`/`OracleRealizableFor`/`ProjectionUniform`;
   the subsumption theorems below show that a sound value oracle induces a
   complete branching oracle, and a realizable+uniform oracle induces a sound
   branching oracle. -/

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

/-- A realizable, uniform oracle induces a sound branching oracle. -/
theorem BranchOracleSoundFor_of_OracleRealizable {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_realizable : OracleRealizableFor H_I π R)
    (h_uniform : ProjectionUniform H_I π) :
    BranchOracleSoundFor H_I π (BranchingOracle.ofValueOracle R) := by
  intro σ ℓ ⟨x', hR⟩
  obtain ⟨σ₀, σ₀', hπ₀, hstep₀, hπ₀'⟩ := h_realizable _ _ _ hR
  obtain ⟨σ', hstep', _⟩ := h_uniform σ₀ σ ℓ x' hπ₀ ⟨σ₀', hstep₀, hπ₀'⟩
  exact ⟨σ', hstep'⟩

/-! ## Oracle-Induced Simulation and Bisimulation

These theorems are the payoff of the oracle conditions — short proofs because
the oracle conditions already did the heavy lifting.

**Forward** (`simulation_of_sound_oracle`): `OracleSoundFor` → oracle LTS
simulates `H_I`. Every concrete step `σ →ℓ σ'` yields `R ℓ (π σ) (π σ')`
directly, which is a step in the oracle LTS. The witness relation is
`fun x σ => π σ = x ∧ H_I.Reachable σ`.

**Reverse** (`simulation_of_complete_oracle`): `OracleRealizableFor +
ProjectionUniform` → `H_I` simulates the oracle LTS. Given oracle claim
`R ℓ x x'` and concrete `σ` with `π σ = x`: realizability finds some `σ₀`
with `π σ₀ = x` that can take the step; uniformity transfers the step to
`σ` itself. The witness relation is `fun σ x => π σ = x`.

**Bisimulation**: both simulations hold simultaneously when all three oracle
conditions hold (`OracleSoundFor`, `OracleRealizableFor`, `ProjectionUniform`).
This is the full correctness guarantee: the extracted oracle LTS and `H_I`
are bisimilar over reachable states. See `CoinductiveBisimulation.lean` for
the coinductive characterization via the general `Learnability.lean` framework.
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

/-- A realizable, uniform oracle induces a reverse simulation: H_I simulates
    the oracle LTS via `fun σ x => π σ = x`. OracleRealizableFor witnesses that
    some concrete step exists; ProjectionUniform transfers it to any concrete
    state with the same projection. -/
theorem simulation_of_complete_oracle {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_realizable : OracleRealizableFor H_I π R)
    (h_uniform : ProjectionUniform H_I π) :
    H_I.Simulates (LTS.ofOracle (π H_I.init) R) (fun σ x => π σ = x) where
  init := rfl
  step_match := by
    intro σ x ℓ x' hrel hstep
    subst hrel
    obtain ⟨σ₀, σ₀', hπ₀, hstep₀, hπ₀'⟩ := h_realizable _ _ _ hstep
    obtain ⟨σ', hstep', hproj⟩ := h_uniform σ₀ σ ℓ x' hπ₀ ⟨σ₀', hstep₀, hπ₀'⟩
    exact ⟨σ', hstep', hproj⟩
