import Learnability

/-!
# Coinductive Bisimulation via Learnability

Capstone of the extraction story. `Learnability.lean` proves that a sound oracle
yields a simulation-equivalent projected model; this file upgrades the result to
**bisimulation** when the oracle is also complete. The file is 127 lines because
no new math is needed — the coinductive proof obligation (show the relation is
preserved by one step) reduces to three theorem applications from
`Learnability.lean`:

- `relevantProjectedOracle_sound` — forward: every implementation step has a
  matching projected oracle step.
- `extractionDims_deproject` — backward: every projected oracle step is
  witnessed by a real implementation step. Uses injectivity (which holds at the
  extraction fixpoint) and completeness.
- `relevant_closed` — threading: relevant states are closed under behavior, so
  the projection relation stays within the relevant fragment at each step.

LTS terminology (bisimulation, simulation) is appropriate here even though
`Learnability.lean` is careful about generality. Bisimulation is inherently an
LTS concept — this file is where the general framework meets the LTS world.

**Connection to `ConditionalSimulation.lean`:** that file establishes *forward*
simulation from oracle soundness alone (no completeness needed). This file
establishes *bisimulation* by adding the backward direction, which requires the
complete oracle (`LearnabilityPreconditionsComplete`). The two files cover the
sound-only and sound+complete cases respectively.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Classical

section CoinductiveBisimulation

variable {State Label Dim Value : Type*}
  [DecidableEq Dim] [Fintype Dim] [Inhabited Value]

/-! ## Grammar LTS

The extracted model is an LTS whose states are projected observations (Dim → Value)
and whose transitions are given by the relevance-restricted projected oracle at
the extraction fixpoint. The relevance restriction is essential: the backward
direction uses injectivity, which only holds on relevant states.
-/

/-- A bisimulation between implementation states and projected grammar states.
    Scoped to relevant implementation states — bisimulation characterizes the
    behavior of reachable states, not the full state space. -/
def IsBisimulation
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (R : State → (Dim → Value) → Prop) : Prop :=
  ∀ s g, R s g → lp.relevant s →
    -- Forward: every implementation step has a matching grammar step
    (∀ ℓ s', lp.behavior s ℓ s' →
      relevantProjectedOracle lp.relevant lp.oracle lp.observe
        lp.extractionDims ℓ g (project lp.observe lp.extractionDims s') ∧
      R s' (project lp.observe lp.extractionDims s')) ∧
    -- Backward: every grammar step has a matching implementation step
    (∀ ℓ g', relevantProjectedOracle lp.relevant lp.oracle lp.observe
        lp.extractionDims ℓ g g' →
      ∃ s', lp.behavior s ℓ s' ∧ R s' g')

/-- The projection relation: implementation state s is related to grammar state g
    when s is relevant and projects to g under the extraction fixpoint. -/
def projectionRelation
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    State → (Dim → Value) → Prop :=
  fun s g => lp.relevant s ∧ project lp.observe lp.extractionDims s = g

/-- The projection relation is a bisimulation.

    This is the main theorem: the inductive fixpoint construction already gives
    us everything we need for bisimulation. The coinductive proof obligation
    (show the relation is preserved by one step) is discharged by:
    - Forward: relevantProjectedOracle_sound
    - Backward: extractionDims_deproject
    - Threading: relevant_closed

    No additional work beyond what the learnability framework already provides. -/
theorem projectionRelation_isBisimulation
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    IsBisimulation lp (projectionRelation lp) := by
  intro s g ⟨hr, hg⟩ _
  subst hg
  constructor
  · -- Forward direction: implementation step → grammar step
    intro ℓ s' hbeh
    exact ⟨lp.relevantProjectedOracle_sound lp.extractionDims s s' ℓ hr hbeh,
           lp.relevant_closed s s' ℓ hr hbeh,
           rfl⟩
  · -- Backward direction: grammar step → implementation step
    intro ℓ g' hclaim
    obtain ⟨s', hbeh, hproj⟩ := lp.extractionDims_deproject hr hclaim
    exact ⟨s', hbeh, lp.relevant_closed s s' ℓ hr hbeh, hproj⟩

/-! ## Bisimilarity as Greatest Fixpoint

Bisimilarity is defined relationally as the union of all bisimulations — the
standard Milner construction, equivalent to the coinductive greatest fixpoint
in classical logic.

Lean 4 does have native `coinductive` predicates (via `Lean.Elab.Coinductive`,
elaborated through partial fixpoint machinery). The Milner construction was
originally chosen under the incorrect belief that `coinductive` was not
available. It works fine — but a coinductive encoding may be cleaner. Open
questions: how `coinductive` interacts with the relevance guard (`lp.relevant s`)
and with `open Classical`.
-/

/-- Two states are bisimilar if they are related by some bisimulation. -/
def Bisimilar
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (s : State) (g : Dim → Value) : Prop :=
  ∃ R, IsBisimulation lp R ∧ R s g

/-- Bisimilarity itself is a bisimulation (it's the union of all bisimulations). -/
theorem bisimilar_isBisimulation
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    IsBisimulation lp (Bisimilar lp) := by
  intro s g ⟨R, hR_bisim, hRsg⟩ hr
  obtain ⟨hfwd, hbwd⟩ := hR_bisim s g hRsg hr
  constructor
  · intro ℓ s' hbeh
    obtain ⟨hgram, hRs'⟩ := hfwd ℓ s' hbeh
    exact ⟨hgram, R, hR_bisim, hRs'⟩
  · intro ℓ g' hclaim
    obtain ⟨s', hbeh, hRs'g'⟩ := hbwd ℓ g' hclaim
    exact ⟨s', hbeh, R, hR_bisim, hRs'g'⟩

/-- The projection relation is contained in bisimilarity:
    every relevant state is bisimilar to its projection. -/
theorem projection_bisimilar
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (s : State) (hr : lp.relevant s) :
    Bisimilar lp s (project lp.observe lp.extractionDims s) :=
  ⟨projectionRelation lp, projectionRelation_isBisimulation lp, hr, rfl⟩

end CoinductiveBisimulation
