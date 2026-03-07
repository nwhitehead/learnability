import Mathlib.Logic.Relation

/-!
# Labeled Transition Systems

Pure theory of labeled transition systems: the vocabulary everything else in
this project builds on. This file is domain-agnostic — no oracles, no
projections, no extraction. Those belong to `ConditionalSimulation.lean` and
downstream.

## Why relational encoding

An LTS is a triple `(S, L, →)` where `→ ⊆ S × L × S`. We encode the
transition relation as `step : S → L → S → Prop` rather than a function
`S → L → S` or `S → L → Option S`. The relational encoding handles
nondeterminism naturally: a state can have multiple successors for the same
label (branching), or none (the transition is unavailable). This is
essential — real implementations branch, and the whole point of extraction
is to recover that branching structure.

The same data, viewed differently, is a Kleisli arrow for the powerset
monad: `step : S → L → Set S`. No conversion is needed — `Set S` is
definitionally `S → Prop` in Lean. The Kleisli perspective is how symbolic
execution actually operates: given a state and a label, enumerate the set of
reachable successors.

## What this file defines

- **LTS structure**: initial state + transition relation.
- **Reachability**: label-erased reflexive-transitive closure via Mathlib's
  `ReflTransGen`. We erase labels because reachability asks "can you get
  there?" not "how?" — the path witness is a trace (below).
- **Traces**: the labeled counterpart to reachability. A trace is a list of
  labels witnessing a step-by-step path between two states. Where
  reachability forgets the path, traces retain it. This duality — reachability
  for existence, traces for evidence — recurs throughout.
- **Branch points and maximal traces**: a branch point has multiple distinct
  outgoing transitions; a dead end has none. A maximal trace extends through
  all deterministic steps, stopping only at branch points or dead ends.
  This captures "faithful execution record" — the trace doesn't stop early
  at a state with a unique successor.
- **Simulation**: `simulating` simulates `simulated` via witness relation
  `R` when initial states are related and every step of `simulated` can be
  matched. Simulation forms a preorder — reflexive via `Eq`, transitive via
  relational composition. This is the standard behavioral preorder on
  abstractions: if A simulates B, then A is at least as behaviorally rich
  as B.
- **Trace inclusion**: simulation implies trace inclusion — every trace of
  the simulated system has a matching trace (same label sequence) in the
  simulating system. This is the standard `simulation ⊆ trace inclusion`
  result.

## What this file does NOT define

No projections, no oracles, no dimension refinement, no extraction. This is
pure LTS theory — the foundation layer. Domain-specific content starts in
`ConditionalSimulation.lean` (projections and oracles) and
`Convergence.lean` (iterative refinement). The general framework in
`Learnability.lean` doesn't import this file at all — it works with
arbitrary `State → Label → State → Prop` behavior relations that need not
be transition systems.
-/

/-! ## Labeled Transition Systems

An LTS over states `S` and labels `L`: an initial state and a transition
relation. Well-formedness (types match, step is of the right sort) is
enforced by Lean's type system—the analog of `→ ⊆ S × L × S` and `s₀ ∈ S`
in the set-theoretic definition.
-/

/-- A labeled transition system (relational encoding). -/
structure LTS (S : Type*) (L : Type*) where
  init : S
  step : S → L → S → Prop

namespace LTS

variable {S L : Type*}

/-- The step relation `S → L → S → Prop` is definitionally `S → L → Set S`
    (the powerset monad / Kleisli arrow). No conversion needed—just
    a change of perspective. -/
example (lts : LTS S L) : S → L → Set S := lts.step


/-! ### Reachability

We erase labels to get a binary relation on states, then use Mathlib's
`Relation.ReflTransGen` for the reflexive-transitive closure. This gives
us transitivity, single-step lifting, and induction principles for free.
-/

/-- The label-erased step relation: `s` can step to `s'` via some label. -/
def canStep (lts : LTS S L) (s s' : S) : Prop :=
  ∃ l, lts.step s l s'

/-- A state is reachable if it is in the reflexive-transitive closure
    of `canStep` from `init`. Corresponds to `Reach(H_I)` in the paper. -/
def Reachable (lts : LTS S L) (s : S) : Prop :=
  Relation.ReflTransGen lts.canStep lts.init s

theorem Reachable.init (lts : LTS S L) : lts.Reachable lts.init :=
  Relation.ReflTransGen.refl

theorem Reachable.step {lts : LTS S L} {s s' : S} {l : L}
    (hr : lts.Reachable s) (hs : lts.step s l s') : lts.Reachable s' :=
  hr.tail ⟨l, hs⟩


/-! ### Traces

A trace is a list of labels witnessing a path between two states.
This is the labeled counterpart to reachability — where `Reachable`
forgets labels, `IsTrace` retains them. Corresponds to the paper's τ ∈ T.
-/

/-- A valid trace: a list of labels witnessing a step-by-step path. -/
inductive IsTrace (lts : LTS S L) : S → List L → S → Prop where
  | nil (s : S) : IsTrace lts s [] s
  | cons (l : L) {s₁ s₂ s₃ : S} (ls : List L) :
      lts.step s₁ l s₂ → IsTrace lts s₂ ls s₃ → IsTrace lts s₁ (l :: ls) s₃

theorem IsTrace.append {lts : LTS S L} {s₁ s₂ s₃ : S} {ls₁ ls₂ : List L}
    (h₁ : IsTrace lts s₁ ls₁ s₂) (h₂ : IsTrace lts s₂ ls₂ s₃) :
    IsTrace lts s₁ (ls₁ ++ ls₂) s₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons l ls hs _ ih => exact .cons l (ls ++ ls₂) hs (ih h₂)

/-- Any trace witnesses a `ReflTransGen` path (label-erased). -/
theorem IsTrace.toReflTransGen {lts : LTS S L} {s₁ s₂ : S} {ls : List L}
    (h : IsTrace lts s₁ ls s₂) : Relation.ReflTransGen lts.canStep s₁ s₂ := by
  induction h with
  | nil => exact .refl
  | cons l _ hs _ ih => exact .head ⟨l, hs⟩ ih

/-- A trace from `init` witnesses reachability of the endpoint. -/
theorem IsTrace.toReachable {lts : LTS S L} {ls : List L} {s : S}
    (h : IsTrace lts lts.init ls s) : lts.Reachable s :=
  h.toReflTransGen

/-- Label determinism implies trace determinism: if every label has at most
    one target from each state, then two traces with the same start state
    and same label sequence must end at the same state. -/
theorem IsTrace.deterministic {lts : LTS S L} {s s₁ s₂ : S} {ls : List L}
    (h_det : ∀ (σ σ₁ σ₂ : S) (ℓ : L), lts.step σ ℓ σ₁ → lts.step σ ℓ σ₂ → σ₁ = σ₂)
    (ht₁ : lts.IsTrace s ls s₁) (ht₂ : lts.IsTrace s ls s₂) : s₁ = s₂ := by
  induction ht₁ with
  | nil => cases ht₂; rfl
  | cons l _ hstep₁ _ ih =>
    cases ht₂ with
    | cons _ _ hstep₂ htrace₂ =>
      exact ih (h_det _ _ _ _ hstep₁ hstep₂ ▸ htrace₂)

/-- Split a trace at a label prefix: a trace over `ls₁ ++ ls₂` decomposes
    into a prefix trace over `ls₁` and a suffix trace over `ls₂`. -/
theorem IsTrace.split_at_prefix {lts : LTS S L} {s s' : S} {ls₁ ls₂ : List L}
    (h : lts.IsTrace s (ls₁ ++ ls₂) s') :
    ∃ s_mid, lts.IsTrace s ls₁ s_mid ∧ lts.IsTrace s_mid ls₂ s' := by
  induction ls₁ generalizing s with
  | nil => exact ⟨s, .nil s, h⟩
  | cons l ls₁' ih =>
    cases h with
    | cons _ _ hstep htail =>
      obtain ⟨s_mid, h₁, h₂⟩ := ih htail
      exact ⟨s_mid, .cons l ls₁' hstep h₁, h₂⟩

/-! ### Branch Points and Maximal Traces

A branch point is a state with multiple possible transitions.
A dead end has no outgoing transitions. A maximal trace extends
through all deterministic steps, terminating only at branch points
or dead ends — capturing the notion of "faithful execution record."
-/

/-- A state is a branch point: it has at least two distinct outgoing
    transitions (differing in label, target, or both). -/
abbrev IsBranchPoint (lts : LTS S L) (s : S) : Prop :=
  ∃ (ℓ₁ : L) (s₁ : S) (ℓ₂ : L) (s₂ : S),
    (ℓ₁ ≠ ℓ₂ ∨ s₁ ≠ s₂) ∧ lts.step s ℓ₁ s₁ ∧ lts.step s ℓ₂ s₂

/-- A state is a dead end: no outgoing transitions. -/
abbrev IsDeadEnd (lts : LTS S L) (s : S) : Prop :=
  ¬∃ (ℓ : L) (s' : S), lts.step s ℓ s'

/-- A maximal trace: extends through all deterministic steps, terminating
    only at a branch point or dead end. This is a "faithful execution
    record" — the trace doesn't stop early at a state with a unique
    successor. -/
abbrev IsMaximalTrace (lts : LTS S L) (s : S) (ls : List L) (s' : S) : Prop :=
  lts.IsTrace s ls s' ∧ (lts.IsBranchPoint s' ∨ lts.IsDeadEnd s')

/-! ### Simulation

`simulating` simulates `simulated` via relation `R` when initial states are
related and every step of `simulated` from a related pair can be matched by
`simulating` preserving `R`.

The paper's `G' ≼ H_I` is simulation between LTS with different state spaces
(X for G', Σ for H_I) mediated by the projection π. We define simulation
generically over any witness relation `R : S₁ → S₂ → Prop`.

Simulation forms a preorder: it is reflexive (via `Eq`) and transitive
(via relational composition).
-/

/-- `simulating` simulates `simulated` via witness relation `R`:
    initial states are related, and every step of `simulated` from a
    related pair can be matched by `simulating` preserving `R`. -/
structure Simulates {S₁ S₂ : Type*}
    (simulating : LTS S₁ L) (simulated : LTS S₂ L)
    (R : S₁ → S₂ → Prop) : Prop where
  init : R simulating.init simulated.init
  step_match : ∀ (s₁ : S₁) (s₂ : S₂) (l : L) (s₂' : S₂),
      R s₁ s₂ → simulated.step s₂ l s₂' →
      ∃ s₁' : S₁, simulating.step s₁ l s₁' ∧ R s₁' s₂'

/-- Simulation is reflexive: any LTS simulates itself via `Eq`. -/
theorem Simulates.refl (lts : LTS S L) : lts.Simulates lts Eq where
  init := rfl
  step_match := by
    intro s₁ s₂ l s₂' heq hstep
    subst heq
    exact ⟨s₂', hstep, rfl⟩

/-- Simulation is transitive: compose witness relations. -/
theorem Simulates.trans {S₁ S₂ S₃ : Type*}
    {lts₁ : LTS S₁ L} {lts₂ : LTS S₂ L} {lts₃ : LTS S₃ L}
    {R₁₂ : S₁ → S₂ → Prop} {R₂₃ : S₂ → S₃ → Prop}
    (h₁₂ : lts₁.Simulates lts₂ R₁₂) (h₂₃ : lts₂.Simulates lts₃ R₂₃) :
    lts₁.Simulates lts₃ (fun s₁ s₃ => ∃ s₂, R₁₂ s₁ s₂ ∧ R₂₃ s₂ s₃) where
  init := ⟨lts₂.init, h₁₂.init, h₂₃.init⟩
  step_match := by
    intro s₁ s₃ l s₃' ⟨s₂, hr₁₂, hr₂₃⟩ hstep₃
    obtain ⟨s₂', hstep₂, hr₂₃'⟩ := h₂₃.step_match s₂ s₃ l s₃' hr₂₃ hstep₃
    obtain ⟨s₁', hstep₁, hr₁₂'⟩ := h₁₂.step_match s₁ s₂ l s₂' hr₁₂ hstep₂
    exact ⟨s₁', hstep₁, s₂', hr₁₂', hr₂₃'⟩

/-- Existential simulation: some witness relation exists.
    Corresponds to `G' ≼ H_I` in the paper. -/
def Sim {S₁ S₂ : Type*} (simulating : LTS S₁ L) (simulated : LTS S₂ L) : Prop :=
  ∃ R : S₁ → S₂ → Prop, simulating.Simulates simulated R


/-! ### Simulation implies Trace Inclusion

Simulation preserves traces: if A simulates B, then every trace of B
has a matching trace in A with the same label sequence. This is the
standard "simulation ⊆ trace inclusion" result.
-/

/-- Simulation implies trace inclusion: if A simulates B via R,
    then any trace of B from a related state has a matching trace
    in A with the same label sequence, ending in a related state. -/
theorem Simulates.trace_inclusion {S₁ S₂ : Type*} {L : Type*}
    {simulating : LTS S₁ L} {simulated : LTS S₂ L}
    {R : S₁ → S₂ → Prop}
    (hsim : simulating.Simulates simulated R)
    {s₁ : S₁} {s₂ : S₂} {ls : List L} {s₂' : S₂}
    (hrel : R s₁ s₂) (htrace : simulated.IsTrace s₂ ls s₂') :
    ∃ s₁' : S₁, simulating.IsTrace s₁ ls s₁' ∧ R s₁' s₂' := by
  induction htrace generalizing s₁ with
  | nil => exact ⟨s₁, .nil s₁, hrel⟩
  | cons l ls hstep _ ih =>
    obtain ⟨s₁_mid, hstep₁, hrel_mid⟩ := hsim.step_match s₁ _ l _ hrel hstep
    obtain ⟨s₁', htrace₁, hrel'⟩ := ih hrel_mid
    exact ⟨s₁', .cons l ls hstep₁ htrace₁, hrel'⟩

end LTS
