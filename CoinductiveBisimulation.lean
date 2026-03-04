import Learnability

/-!
# Coinductive Bisimulation via Learnability

Capstone of the extraction story. `Learnability.lean` proves that a sound oracle
yields a simulation-equivalent projected model; this file upgrades the result to
**bisimulation** when the oracle is also complete. The file is short because
no new math is needed — the coinductive proof obligation (if a property holds
now and is preserved by every transition, then it holds at all future times)
reduces to three theorem applications from
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
standard Milner construction. The idea: define "bisimilar" as "related by
*some* bisimulation R," then show that bisimilarity itself is a bisimulation
(because the union of bisimulations is a bisimulation). This makes it the
greatest fixpoint of the one-step matching operator — equivalent to the
coinductive definition in classical logic.

Lean 4 does have native `coinductive` predicates (via `Lean.Elab.Coinductive`,
elaborated through partial fixpoint machinery). The Milner construction was
originally chosen under the incorrect belief that `coinductive` was not
available. Both encodings now coexist — see the `BisimilarCo` section below
for the coinductive version and the equivalence proof.
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

/-! ## Coinductive Encoding

The same bisimilarity, defined directly as a `coinductive` predicate rather than
as the union of all bisimulations. Lean 4's `coinductive` elaborates through
partial fixpoint machinery and generates a coinduction principle
(`BisimilarCo.coinduct`) automatically.

The two encodings are equivalent on relevant states. The Milner construction
(`Bisimilar`) is more explicit — you can see the witness bisimulation. The
coinductive version (`BisimilarCo`) is more direct — bisimilarity means the
one-step property holds forever, no intermediate `IsBisimulation` needed.

Note: `BisimilarCo` requires `lp.relevant s` in its constructor, making
relevance a structural invariant. `Bisimilar` is vacuously true for irrelevant
states (since `IsBisimulation` only constrains relevant pairs). The equivalence
therefore holds on relevant states, which is the only case that matters —
`projection_bisimilar` and `projection_bisimilarCo` both take `hr : lp.relevant s`.
-/

section CoinductiveBisimulationCo

variable {State Label Dim Value : Type*}
  [DecidableEq Dim] [Fintype Dim] [Inhabited Value]

open Classical

/-- Bisimilarity defined coinductively: two states are bisimilar when the
    one-step matching property holds at every depth. Equivalent to `Bisimilar`
    on relevant states. -/
coinductive BisimilarCo
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    : State → (Dim → Value) → Prop where
  | step : ∀ s g,
    lp.relevant s →
    (∀ ℓ s', lp.behavior s ℓ s' →
      relevantProjectedOracle lp.relevant lp.oracle lp.observe
        lp.extractionDims ℓ g (project lp.observe lp.extractionDims s') ∧
      BisimilarCo lp s' (project lp.observe lp.extractionDims s')) →
    (∀ ℓ g', relevantProjectedOracle lp.relevant lp.oracle lp.observe
        lp.extractionDims ℓ g g' →
      ∃ s', lp.behavior s ℓ s' ∧ BisimilarCo lp s' g') →
    BisimilarCo lp s g

/-- The coinductive bisimilarity is a bisimulation in the relational sense.
    Unfold one step of the coinductive definition. -/
theorem bisimilarCo_isBisimulation
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    IsBisimulation lp (BisimilarCo lp) := by
  intro s g hco hr
  cases hco with
  | step _ _ _ hfwd hbwd => exact ⟨hfwd, hbwd⟩

/-- Coinductive bisimilarity implies Milner bisimilarity: `BisimilarCo` is
    itself a bisimulation, so it witnesses the existential in `Bisimilar`. -/
theorem bisimilarCo_implies_bisimilar
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (s : State) (g : Dim → Value) :
    BisimilarCo lp s g → Bisimilar lp s g :=
  fun hco => ⟨BisimilarCo lp, bisimilarCo_isBisimulation lp, hco⟩

/-- Milner bisimilarity implies coinductive bisimilarity (for relevant states).

    Uses `BisimilarCo.coinduct` — the coinduction principle Lean 4 generates
    automatically. The coinduction predicate is `fun s g => relevant s ∧ Bisimilar s g`,
    strengthened with relevance because `BisimilarCo.step` requires it.
    `relevant_closed` threads relevance through successor states. -/
theorem bisimilar_implies_bisimilarCo
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (s : State) (g : Dim → Value)
    (hr : lp.relevant s) :
    Bisimilar lp s g → BisimilarCo lp s g := by
  intro hbis
  apply BisimilarCo.coinduct lp (fun s g => lp.relevant s ∧ Bisimilar lp s g)
  · intro a a₁ ⟨hra, R, hR_bisim, hRaa₁⟩
    obtain ⟨hfwd, hbwd⟩ := hR_bisim a a₁ hRaa₁ hra
    refine ⟨hra, ?_, ?_⟩
    · intro ℓ s' hbeh
      obtain ⟨hgram, hRs'⟩ := hfwd ℓ s' hbeh
      exact ⟨hgram, lp.relevant_closed a s' ℓ hra hbeh, R, hR_bisim, hRs'⟩
    · intro ℓ g' hclaim
      obtain ⟨s', hbeh, hRs'g'⟩ := hbwd ℓ g' hclaim
      exact ⟨s', hbeh, lp.relevant_closed a s' ℓ hra hbeh, R, hR_bisim, hRs'g'⟩
  · exact ⟨hr, hbis⟩

/-- Every relevant state is coinductively bisimilar to its projection.
    The coinductive analog of `projection_bisimilar`. -/
theorem projection_bisimilarCo
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (s : State) (hr : lp.relevant s) :
    BisimilarCo lp s (project lp.observe lp.extractionDims s) :=
  bisimilar_implies_bisimilarCo lp s _ hr (projection_bisimilar lp s hr)

end CoinductiveBisimulationCo
