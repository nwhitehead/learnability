import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
# The Learnability Framework

General framework for extracting faithful behavioral models from arbitrary
observable systems via iterative dimension refinement. **This file imports
only Mathlib** — it is independent of `LTS.lean`, `ConditionalSimulation.lean`,
and `Convergence.lean`. The `behavior : State → Label → State → Prop` field
does not require an LTS interpretation.

## The Core Claim

Any system with (1) finite behavioral structure, (2) identifiable observations,
and (3) a sound oracle admits faithful extraction of a projected behavioral model
via iterative refinement. With a sound oracle the extracted model is
simulation-equivalent to the original over relevant states; with a complete
oracle the relationship upgrades to bisimulation.

"Finite behavioral structure" means the observation space is finite —
`[Fintype Dim]`. This does NOT mean finitely many states. A terminal emulator
has an infinite state space (the screen buffer), but finitely many behavioral
distinctions (the escape sequence parser operates over finitely many modes and
control characters). `[Fintype Dim]` bounds the observation space, not the
system's reachable state space.

## Structure of This File

1. `ObservableSystem` — base structure: relevant states, behavior relation,
   observation function
2. `LearnabilityPreconditions` — identifiable + sound oracle
3. Refinement machinery: `project`, `projectedOracle`, `refineStep`
4. Monotone stabilization: self-contained proof of `inflationary_stabilizes_bound`
5. `extraction_exists` — fixpoint gives soundness + controllability
6. `extraction_with_projection` — names the extracted π and R explicitly
7. `LearnabilityPreconditionsComplete` — adds `complete` + `relevant_closed`
8. `exact_extraction` — complete oracle gives soundness + controllability + injectivity
9. `relevantProjectedOracle`, `relevantProjectedOracle_witness_eq` —
   relevance-restricted oracle enabling reverse direction
10. Named constructions (sound-only): `extractionDims`,
    `extractionDims_each_dim_witnessed` — concrete fixpoint with certificates
11. Named constructions (complete): `refineStepComplete`, `extractionDims` (complete
    case), `extractionDims_deproject`, `extractionDims_each_dim_witnessed` (complete)

## Three Explicit Preconditions (Plus One Implicit)

The Lean types capture three explicit preconditions:

**1. Finite behavioral structure**: `[Fintype Dim]` — the observation space has
finitely many dimensions. Combined with `[DecidableEq Dim]`, this makes
`refineStep` compute a well-defined `Finset` and ensures
`inflationary_stabilizes_bound` terminates in at most `Fintype.card Dim`
iterations.

**2. Identifiability**: `identifiable` — the observation function
`observe : State → Dim → Value` distinguishes all relevant states. Two states
with identical observations across all dimensions must be the same state. In
practice this is near-trivial for concrete computational objects: for any
`DecidableEq State`, using the identity as the observation function satisfies
identifiability. The interesting question is not whether identifiability holds
but which dimensions are *needed* — that is what `refineStep` discovers.

**3. Sound oracle**: `oracle` + `sound` — every real behavior `behavior s ℓ s'`
has an oracle witness `oracle ℓ s s'`. In the symex instantiation, KLEE (or
similar) plays this role. Symbolic execution runs a program on symbolic inputs
rather than concrete ones, exploring all execution paths and collecting the
logical conditions (path conditions) under which each path is taken. This
yields oracle witnesses for all reachable behaviors. This is the non-trivial
precondition in practice — building the oracle requires engineering.

**Fourth implicit precondition (not in the Lean types): Effective observability.**
The oracle must be *productive*: given an incorrect candidate dimension set X,
the oracle finds a distinguishing witness pair rather than returning ⊥ forever.

In the OGIS framework (Jha & Seshia, *Acta Informatica* 2018), this is the
"productive q_ce oracle" property: a counterexample query oracle that eventually
returns a counterexample on incorrect hypotheses, even though it may return ⊥ on
any individual query. Symbolic execution is naturally such an oracle — sound but
partial (may time out or exhaust paths on any single query).

Effective observability holds when three conditions align:

- The implementation has a **reducible control-flow graph** (standard for
  compiled C; necessary for program dependence graph construction).
- Decision points have **thin semantic backward slices** — branch conditions
  depend on few variables, making path conditions tractable.
- Path conditions fall in a **decidable theory**: QF_BV (quantifier-free
  bitvector arithmetic, decidable via SAT reduction), linear arithmetic
  (also decidable), but not nonlinear integer arithmetic (undecidable).

The Lean types say `noncomputable` + `Classical` for `refineStep` and
`extractionDims` precisely because effective observability is not yet formalized:
classical logic witnesses the existence of distinguishing pairs without
constructing them. Formalizing when the oracle is productive is an open problem —
it is what this research program is working toward.

## Controllability and Separability Are Derived, Not Assumed

Two properties that might look like additional preconditions are in fact
*consequences* of the fixpoint:

- **Controllability**: states with the same projection have the same behavior
  availability (`extraction_exists` proves this at the fixpoint).
- **Injectivity** (separability): the projection is injective on relevant states
  (`exact_extraction`, `extractionDims_injective` — complete oracle case only).

The fixpoint argument for controllability: if two relevant states have the same
X-projection but different behavior availability, `refineStep` would add a
distinguishing dimension — contradicting fixpoint. These properties emerge from
identifiability + fixpoint; they are not inputs.

## Refinement Mechanics

`refineStep sys X` produces the next dimension set by adding every dimension `d`
that witnesses a non-controllability disagreement at the current projection X:

```
X ∪ {d | ∃ s₁ s₂ ℓ, relevant s₁ ∧ s₁ can take ℓ ∧
                    s₂ has the same X-projection as s₁ ∧
                    s₂ cannot take ℓ ∧
                    s₁ and s₂ differ at d}
```

Path-condition reading: "find two situations the current model conflates (same
X-projection) but that behave differently (one can take ℓ, the other cannot), and
add the dimension that distinguishes them." Each added dimension corresponds to a
path condition separating these states.

Non-circularity: the oracle witnesses are drawn from actual `State` values, not
from the projected `Dim → Value` space. What dimensions matter is discovered
from the full state space, independent of which dimensions X currently tracks.

## Convergence and Complexity

`inflationary_stabilizes_bound` proves that `refineStep` terminates in at most
`Fintype.card Dim` iterations: the operator is inflationary (only adds dimensions),
and the cardinality strictly increases with each non-fixpoint step, bounded by
`|Dim|`. Translated to oracle calls: extraction costs O(|Dim| × oracle_cost).

**Finding a fixpoint is tractable. Finding the *minimum* fixpoint is NP-hard.**

The dimension set `extractionDims` is *a* faithful fixpoint — not necessarily the
minimum one. Every tracked dimension has a concrete certificate of necessity
(`extractionDims_each_dim_witnessed`): it was added because specific states
(s₁, s₂) and label ℓ demonstrated its necessity at some refinement step k. But a
smaller fixpoint may exist that also distinguishes all relevant behaviors.

This is not a deficiency — it is provably optimal *not* to claim minimality.
Finding the minimum faithful dimension set is NP-hard by reduction from minimum
set cover (Jha & Seshia 2018, Theorem 6.1). Behavioral distinctions map to the
elements to be covered; dimensions map to sets; a minimum faithful dimension set
is a minimum cover. `refineStep` finds a valid fixpoint greedily, not an optimal
one.

The number of refinement iterations is lower-bounded by the teaching dimension TD
of the concept class (Goldman & Kearns 1995; Jha & Seshia Theorem 6.2: M_OGIS ≥
TD). Together with `inflationary_stabilizes_bound`:

```
TD(concept class) ≤ actual iterations ≤ Fintype.card Dim
```

## Two Extraction Modes

**Sound oracle only — `LearnabilityPreconditions`:** Yields soundness and
controllability at the fixpoint. In the LTS instantiation (via
`ConditionalSimulation.lean`), this gives forward simulation: G' simulates H_I
over relevant states.

**Complete oracle — `LearnabilityPreconditionsComplete`:** Additionally requires
`complete` (oracle witness → real behavior) and `relevant_closed` (behavior
preserves relevance). Uses `refineStepComplete`, which adds dimensions both for
non-controllability disagreements and for relevant-state observation disagreements.
At this fixpoint, the projection is injective on relevant states. Combined with
`relevantProjectedOracle` and `extractionDims_deproject`, this gives the reverse
simulation direction, assembling to bisimulation. See `CoinductiveBisimulation.lean`
for the assembled proof.

## Seven Target Domains

The framework handles any `behavior : State → Label → State → Prop` — the fields
need not represent state transitions:

1. **Operational semantics** (LTS): clean fit. `behavior = step`,
   `relevant = Reachable`. Path conditions from symex separate control-flow
   distinctions directly. This is the primary instantiation in the project.

2. **Parsing / recursive descent parsers**: `behavior` captures parse derivations.
   The implementation complexity (stack manipulation, lookahead) hides the grammar
   structure that `refineStep` recovers.

3. **Terminal emulation**: escape sequence processing as an LTS. Infinite screen
   state space, finitely many escape sequence modes — `[Fintype Dim]` captures the
   finite behavioral structure.

4. **Type systems**: `behavior` captures typing judgments (Γ ⊢ e : τ), not state
   transitions. `State := (Context × Expr)`, `Label := TypeRule` (which typing rule
   applies), `behavior (Γ, e) rule (Γ', e')` means applying `rule` in context Γ to
   expression e yields context Γ' and subexpression e'. `Dim` ranges over context
   shapes — the finite set of relevant context distinctions (e.g., "is variable x
   bound?", "what is the type of variable y?"). No initial state — judgments stand
   alone, so `relevant` filters to well-formed `(Γ, e)` pairs rather than marking
   reachable states. Identifiability is trivially `DecidableEq` on `(Context × Expr)`.
   Finitely many type rules and context shapes give `[Fintype Dim]`.

5. **Effect systems**: `behavior` captures effect propagation constraints, not state
   transitions. `State := (EffectContext × Computation)`, `Label := EffectOperation`
   (which effect operation is performed), `behavior (ε, c) op (ε', c')` means
   performing operation `op` in effect context ε on computation c yields ε' and c'.
   `Dim` ranges over effect annotations — the finite set of effect distinctions
   tracked by the system (e.g., "does this computation perform IO?", "is this
   handler installed?"). Effect annotations propagate through the type system, not
   through state transitions — a genuinely different mechanism from LTS, but
   `ObservableSystem` handles it because `behavior` is just a relation on states.

6. **Effect handler operational semantics**: a clean LTS — in contrast to #5,
   which is not an LTS. The effect annotation system and its operational semantics
   live in different categories despite describing the same language feature.

7. **Module systems / namespace resolution**: binding and resolution relations.
   Less developed as a target domain.

The non-LTS examples (#4, #5) sharpen the generality claim. `ObservableSystem`'s
`behavior : State → Label → State → Prop` doesn't care whether the relation
represents transitions, judgments, or constraint propagation.

**Framework power is proportional to implementation opacity.** When the behavior
structure is directly readable from the binary, no extraction is needed. When the
grammar or semantics is buried in control flow — as in recursive descent parsers
or terminal emulators — `refineStep` pays for itself.

## Relation to Convergence.lean and ConditionalSimulation.lean

Those files implement the same technique for the specific LTS case:
`CoRefinementProcess` iterates dimension refinement operationally, and
`simulation_at_coRefinement_fixpoint` gives the forward simulation result.
The present file is more general (any `ObservableSystem`), more declarative
(existence of a fixpoint rather than construction), and more complete (bisimulation
via the complete oracle case). The two developments are bridged in `LearnabilityConvergence.lean`:
any `LearnabilityPreconditions` instance gives rise to a `CoRefinementProcess`,
and `extractionDims` is a valid co-refinement fixpoint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Observable Systems

A system with observable state and labeled behavior. NOT necessarily
an LTS — the behavior relation captures whatever aspect of semantics
we're studying (transitions, typing judgments, parse relations, etc.).
-/

/-- A system with observable state and labeled behavior.
    NOT necessarily an LTS — the behavior relation captures whatever
    aspect of semantics we're studying (transitions, typing judgments,
    parse relations, etc.). -/
structure ObservableSystem (State Label Dim Value : Type*)
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value] where
  /-- Which states are relevant (Reachable for LTS, well-typed for
      type systems, valid inputs for parsers, etc.) -/
  relevant : State → Prop
  /-- The behavior relation we're trying to model. For LTS: step.
      For typing: hasType. For parsing: parses. -/
  behavior : State → Label → State → Prop
  /-- Observation function (identifiability mechanism) -/
  observe : State → Dim → Value

/-! ## Learnability Preconditions

Three explicit preconditions bundled as a Lean structure extending
ObservableSystem. See the module docstring for the full precondition
analysis including the implicit fourth (effective observability).
-/

/-- Learnability preconditions for semantic extraction.

    Any observable system satisfying these conditions admits extraction
    of an identifiable projected model via iterative refinement.

    Three explicit preconditions:
    1. **Finite behavioral structure**: `[Fintype Dim]` — the observation
       space is finite (typeclass, not a field — shared with `ObservableSystem`)
    2. **Identifiability**: `identifiable` — observations distinguish
       relevant states (injective on relevant states, unconstrained on s₂)
    3. **Sound oracle**: `oracle` + `sound` — every real behavior has an
       oracle witness

    Controllability (same projection → same behavior availability) and
    injectivity (projection injective on relevant states) are *derived*
    at the refinement fixpoint, not assumed. See `extraction_exists` and
    `exact_extraction`.

    The abstract statement covers any system expressible as
    State → Label → State → Prop; instantiating the preconditions
    for domains beyond operational semantics may be non-trivial. -/
structure LearnabilityPreconditions
    (State Label Dim Value : Type*)
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    extends ObservableSystem State Label Dim Value where
  /-- Identifiability: observations are injective on relevant states.
      Any relevant state is uniquely determined by its observations
      among ALL states (s₂ unconstrained). -/
  identifiable : ∀ (s₁ s₂ : State), relevant s₁ →
    (∀ d, observe s₁ d = observe s₂ d) → s₁ = s₂
  /-- Sound oracle for the system's behavior -/
  oracle : Label → State → State → Prop
  /-- Oracle soundness: every real behavior has an oracle witness -/
  sound : ∀ (s s' : State) (ℓ : Label), behavior s ℓ s' → oracle ℓ s s'

/-! ## Identifiability Theorems

The `identifiable` precondition — observations distinguish relevant states —
is near-trivially satisfiable for concrete computational objects. These
theorems make that precise.

**What this discharges and what it doesn't.** Identifiability is the *easy*
precondition. For any system with decidable state equality (programs on x86,
ARM, any concrete ISA), these theorems give you identifiability for free.
The *hard* preconditions — constructing a sound oracle (requires symbolic
execution or equivalent) and achieving effective observability (the fourth
implicit precondition: choosing *what* to observe, building instrumentation
harnesses, computing the right program slice) — are not addressed here.
The framework guarantees convergence *if* you solve those problems; these
theorems just ensure identifiability won't be the bottleneck.
-/

/-- Globally injective observation implies identifiability.

    If `observe`, viewed as a function `State → (Dim → Value)`, is injective,
    then the `identifiable` precondition holds for any `relevant` predicate.

    Relevance is unused — global injectivity is stronger than the precondition
    requires. The precondition only constrains `relevant s₁` (with `s₂`
    unconstrained), so an observation function may conflate irrelevant states
    with each other, as long as no irrelevant state is observationally
    identical to a relevant one. -/
theorem identifiable_of_injective_observe
    {State Dim Value : Type*}
    (observe : State → Dim → Value)
    (h_inj : Function.Injective observe)
    {relevant : State → Prop} :
    ∀ (s₁ s₂ : State), relevant s₁ →
      (∀ d, observe s₁ d = observe s₂ d) → s₁ = s₂ :=
  fun s₁ s₂ _ h_obs => h_inj (funext h_obs)

/-- The indicator observation `fun s d => decide (s = d)` is injective.

    For any type with decidable equality, each state has a unique Boolean
    fingerprint: state `s` maps dimension `d` to `true` iff `s = d`.
    Two states with identical fingerprints must be equal. -/
theorem indicator_observe_injective {State : Type*} [DecidableEq State] :
    Function.Injective (fun (s : State) (d : State) => decide (s = d)) := by
  intro s₁ s₂ h
  have h₁ := congr_fun h s₁
  simp at h₁
  exact h₁.symm

/-- Identifiability for `DecidableEq` types via the indicator observation.

    Corollary of `identifiable_of_injective_observe` applied to
    `indicator_observe_injective`. For any concrete computational type
    with decidable equality — `State := (Stack × Heap × Registers)`,
    `State := (Context × Expr)`, etc. — identifiability is trivially
    satisfiable using `Dim := State`, `Value := Bool`,
    `observe s d := decide (s = d)`.

    This proves identifiability is *satisfiable*, not that the indicator
    observation is the right one to use. In practice, the choice of
    observation function determines the quality of the extracted model —
    a natural observation like register/memory reads on an ISA gives a
    meaningful model, while the indicator construction only witnesses
    existence. The hard work is choosing observations that make effective
    observability achievable.

    Note: using this as an `identifiable` field in `LearnabilityPreconditions`
    also requires `[Fintype State]`, since the framework needs `[Fintype Dim]`
    and here `Dim = State`. -/
theorem identifiable_indicator
    {State : Type*} [DecidableEq State]
    {relevant : State → Prop} :
    ∀ (s₁ s₂ : State), relevant s₁ →
      (∀ d : State, decide (s₁ = d) = decide (s₂ = d)) → s₁ = s₂ :=
  identifiable_of_injective_observe (fun s d => decide (s = d)) indicator_observe_injective

/-! ## Refinement Machinery

Standalone definitions for projection, projected oracle, and refinement
step. These are self-contained — no imports from the LTS chain.
-/

/-- Project state onto tracked dimensions, defaulting elsewhere. -/
abbrev project {State Dim Value : Type*}
    [DecidableEq Dim] [Inhabited Value]
    (observe : State → Dim → Value) (X : Finset Dim)
    (s : State) : Dim → Value :=
  fun d => if d ∈ X then observe s d else default

/-- Projected oracle: claims behavior(ℓ, x, x') when witnesses exist. -/
abbrev projectedOracle {State Label Dim Value : Type*}
    [DecidableEq Dim] [Inhabited Value]
    (oracle : Label → State → State → Prop)
    (observe : State → Dim → Value) (X : Finset Dim)
    : Label → (Dim → Value) → (Dim → Value) → Prop :=
  fun ℓ x x' => ∃ s s', project observe X s = x ∧
    oracle ℓ s s' ∧ project observe X s' = x'

open Classical in
/-- Refinement step: add dimensions witnessing non-controllable behavior.
    Dimension d is added when there exist relevant state s₁ (which can
    take some behavior ℓ) and state s₂ (with the same projection but
    unable to take ℓ) that differ at d. -/
noncomputable abbrev refineStep {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (sys : ObservableSystem State Label Dim Value) (X : Finset Dim)
    : Finset Dim :=
  X ∪ Finset.univ.filter (fun d =>
    ∃ (s₁ s₂ : State) (ℓ : Label),
      sys.relevant s₁ ∧
      (∃ s₁', sys.behavior s₁ ℓ s₁') ∧
      project sys.observe X s₂ = project sys.observe X s₁ ∧
      (¬∃ s₂', sys.behavior s₂ ℓ s₂') ∧
      sys.observe s₁ d ≠ sys.observe s₂ d)

/-! ## Monotone Finset Stabilization

An inflationary operator on Finset over Fintype stabilizes.
Self-contained proof (mirrors `Convergence.lean`).
-/

/-- A monotone increasing sequence of finsets over a finite type
    eventually stabilizes: there exists `n` with `s n = s (n + 1)`. -/
theorem Finset.monotone_stabilizes' {α : Type*} [DecidableEq α] [Fintype α]
    (s : ℕ → Finset α) (h_mono : ∀ n, s n ⊆ s (n + 1)) :
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
  have h_upper := Finset.card_le_univ (s (Fintype.card α + 1))
  exact absurd (Nat.le_trans (h_lower _) h_upper) (by omega)

/-- Inflationary operator on Finset over Fintype stabilizes. -/
theorem inflationary_stabilizes {Dim : Type*} [DecidableEq Dim] [Fintype Dim]
    (f : Finset Dim → Finset Dim) (h_infl : ∀ X, X ⊆ f X)
    (X₀ : Finset Dim) : ∃ n, f^[n + 1] X₀ = f^[n] X₀ := by
  have ⟨n, h⟩ := Finset.monotone_stabilizes' (fun n => f^[n] X₀) (fun n => by
    show f^[n] X₀ ⊆ f^[n + 1] X₀
    rw [Function.iterate_succ_apply']
    exact h_infl (f^[n] X₀))
  exact ⟨n, h.symm⟩

/-- Explicit bound: an inflationary operator on Finset over Fintype
    stabilizes in at most `Fintype.card Dim` iterations. This bounds
    the number of co-refinement rounds needed for extraction. -/
theorem inflationary_stabilizes_bound {Dim : Type*} [DecidableEq Dim] [Fintype Dim]
    (f : Finset Dim → Finset Dim) (h_infl : ∀ X, X ⊆ f X)
    (X₀ : Finset Dim) :
    ∃ n, n ≤ Fintype.card Dim ∧ f^[n + 1] X₀ = f^[n] X₀ := by
  by_contra h_none
  push_neg at h_none
  -- h_none : ∀ n, n ≤ Fintype.card Dim → f^[n + 1] X₀ ≠ f^[n] X₀
  -- The chain is strictly increasing for Fintype.card Dim + 1 steps
  have h_ssubset : ∀ n, n ≤ Fintype.card Dim →
      (f^[n] X₀) ⊂ (f^[n + 1] X₀) := by
    intro n hn
    have h_sub : f^[n] X₀ ⊆ f^[n + 1] X₀ := by
      rw [Function.iterate_succ_apply']
      exact h_infl (f^[n] X₀)
    exact h_sub.ssubset_of_ne (h_none n hn).symm
  have h_card_lt : ∀ n, n ≤ Fintype.card Dim →
      (f^[n] X₀).card < (f^[n + 1] X₀).card :=
    fun n hn => Finset.card_lt_card (h_ssubset n hn)
  -- Cardinality grows at least linearly
  have h_lower : ∀ n, n ≤ Fintype.card Dim + 1 → n ≤ (f^[n] X₀).card := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih (by omega)) (h_card_lt n (by omega)))
  -- But cardinality is bounded by Fintype.card Dim
  have h_upper := Finset.card_le_univ (f^[Fintype.card Dim + 1] X₀)
  have h_low := h_lower (Fintype.card Dim + 1) (le_refl _)
  omega


/-- Once an iterated function reaches a fixpoint, it stays there. -/
theorem Function.iterate_stable' {α : Type*}
    (f : α → α) (a : α)
    {n : ℕ} (h_fix : f^[n] a = f^[n + 1] a) :
    ∀ m, f^[n + m] a = f^[n] a := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have h_eq : n + (m + 1) = (n + m) + 1 := Nat.add_assoc n m 1
    conv_lhs => rw [h_eq]
    rw [Function.iterate_succ_apply', ih]
    rw [← Function.iterate_succ_apply' f n a]
    exact h_fix.symm

/-! ## Main Learnability Theorems

The central result is `extraction_exists`: given an `ObservableSystem` with
identifiable observations and a sound oracle, iterative refinement produces a
dimension set at which the projected oracle is sound and all behavior is
controllable. Everything else in this file either builds toward this theorem
or extends it (complete oracle, named constructions, certificates). -/

open Classical in
/-- Main learnability theorem: any system satisfying the three preconditions
    admits an identifiable projected model.

    "Identifiable" means: at the fixpoint tracked dimensions X*,
    (1) the projected oracle is sound for all relevant behaviors, and
    (2) all behavior of relevant states is controllable — if two states
        have the same projection, they have the same behavior availability.

    For LTS: this implies simulation (G' simulates H_I).
    The specific correctness notion is domain-dependent. -/
theorem LearnabilityPreconditions.extraction_exists
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value) :
    ∃ (X : Finset Dim),
      -- Sound: every relevant behavior captured by projected oracle
      (∀ (s s' : State) (ℓ : Label), lp.relevant s → lp.behavior s ℓ s' →
        projectedOracle lp.oracle lp.observe X ℓ
          (project lp.observe X s) (project lp.observe X s')) ∧
      -- Controllable: same projection → same behavior availability
      (∀ (s₁ s₂ : State) (ℓ : Label), lp.relevant s₁ →
        project lp.observe X s₁ = project lp.observe X s₂ →
        (∃ s₁', lp.behavior s₁ ℓ s₁') →
        (∃ s₂', lp.behavior s₂ ℓ s₂')) := by
  -- Find fixpoint of refinement
  let sys : ObservableSystem State Label Dim Value :=
    lp.toObservableSystem
  let refStep := refineStep sys
  have h_infl : ∀ X, X ⊆ refStep X := fun X => Finset.subset_union_left
  obtain ⟨n, h_conv⟩ := inflationary_stabilizes refStep h_infl ∅
  let X := refStep^[n] ∅
  have h_fp : refStep X = X := by
    show refStep (refStep^[n] ∅) = refStep^[n] ∅
    have : refStep^[n + 1] ∅ = refStep^[n] ∅ := h_conv
    rwa [Function.iterate_succ_apply'] at this
  refine ⟨X, ?_, ?_⟩
  -- Soundness: from oracle soundness
  · intro s s' ℓ _hrel hbeh
    exact ⟨s, s', rfl, lp.sound s s' ℓ hbeh, rfl⟩
  -- Controllability: at fixpoint, identifiability makes it vacuous
  · intro s₁ s₂ ℓ h_rel hproj_eq ⟨s₁', hbeh⟩
    by_cases h_can : ∃ s', lp.behavior s₂ ℓ s'
    · exact h_can
    · -- s₂ can't take ℓ. Show s₁ = s₂, contradicting this.
      exfalso; apply h_can
      have h_eq : s₁ = s₂ := by
        apply lp.identifiable _ _ h_rel
        intro d
        by_cases hd : d ∈ X
        · -- d ∈ X: projection equality gives agreement
          have h_pe : (if d ∈ X then lp.observe s₁ d else (default : Value)) =
              (if d ∈ X then lp.observe s₂ d else default) := congr_fun hproj_eq d
          rw [if_pos hd, if_pos hd] at h_pe
          exact h_pe
        · -- d ∉ X: fixpoint ensures d would be in X if they differed
          by_contra h_ne
          have h_mem : d ∈ refStep X := by
            apply Finset.mem_union_right
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ d, s₁, s₂, ℓ, h_rel, ⟨s₁', hbeh⟩,
                   hproj_eq.symm, h_can, h_ne⟩
          rw [h_fp] at h_mem
          exact hd h_mem
      subst h_eq; exact ⟨s₁', hbeh⟩

/-- The soundness conclusion of `extraction_exists` gives an explicit
    projection π and oracle R such that R ℓ (π s) (π s') holds for
    every relevant behavior s →ℓ s'. This is the oracle soundness
    pattern that yields simulation when instantiated with a concrete
    init state (see `simulation_of_sound_oracle` in
    `ConditionalSimulation.lean` for the LTS case).

    In the LTS instantiation: set `relevant = Reachable`,
    `behavior = step`, construct `G' := LTS.ofOracle (π init) R`,
    and this soundness gives `G'.Simulates H_I (fun x σ => π σ = x)`. -/
theorem LearnabilityPreconditions.extraction_with_projection
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value) :
    ∃ (π : State → Dim → Value) (R : Label → (Dim → Value) → (Dim → Value) → Prop),
      -- Sound: every relevant behavior captured by R through π
      (∀ (s s' : State) (ℓ : Label), lp.relevant s → lp.behavior s ℓ s' →
        R ℓ (π s) (π s')) ∧
      -- Controllable: same projection → same behavior availability
      (∀ (s₁ s₂ : State) (ℓ : Label), lp.relevant s₁ →
        π s₁ = π s₂ →
        (∃ s₁', lp.behavior s₁ ℓ s₁') →
        (∃ s₂', lp.behavior s₂ ℓ s₂')) := by
  obtain ⟨X, h_sound, h_ctrl⟩ := lp.extraction_exists
  exact ⟨project lp.observe X, projectedOracle lp.oracle lp.observe X,
    h_sound, h_ctrl⟩

/-! ## Exact Extraction (Complete Oracle)

With a complete oracle, extraction yields an exact model: the projection
is injective on relevant states, giving bisimulation. -/

/-- Learnability preconditions with a complete oracle.
    Together with `sound`, completeness makes the oracle biconditional
    with the behavior relation on all states.

    Note: `exact_extraction` below does not use `complete` or
    `relevant_closed` — it proves soundness, controllability, and
    injectivity from `identifiable` + `sound` alone. These fields are
    present for downstream bisimulation construction, which requires
    completeness to go from projected oracle claims back to real
    behavior, and relevant closure to thread relevance through
    multi-step simulation. -/
structure LearnabilityPreconditionsComplete
    (State Label Dim Value : Type*)
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    extends LearnabilityPreconditions State Label Dim Value where
  /-- Oracle completeness: every oracle claim is a real behavior -/
  complete : ∀ (s s' : State) (ℓ : Label), oracle ℓ s s' → behavior s ℓ s'
  /-- Relevant states are closed under behavior (needed for threading) -/
  relevant_closed : ∀ (s s' : State) (ℓ : Label),
    relevant s → behavior s ℓ s' → relevant s'

open Classical in
/-- With a complete oracle, extraction yields an exact model:
    the projection is injective on relevant states. Combined with
    a relevance-restricted oracle and `relevant_closed`, this gives
    bisimulation (see `CoinductiveBisimulation.lean`).

    The proof only uses `identifiable` and `sound` from the parent
    structure — `complete` and `relevant_closed` are not needed for
    the three properties proved here (soundness, controllability,
    injectivity are all earned before completeness enters). Completeness
    becomes necessary only downstream, when the reverse simulation
    direction needs to go from a projected oracle claim back to real
    behavior (`extractionDims_deproject`).

    The proof uses a combined refinement step that tracks both
    non-controllability disagreements (as in `extraction_exists`) and
    observation disagreements among relevant states. At fixpoint,
    identifiable + no disagreements → injective on relevant states,
    and the non-controllability argument gives controllability. -/
theorem LearnabilityPreconditionsComplete.exact_extraction
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    ∃ (X : Finset Dim),
      -- Sound: every relevant behavior captured
      (∀ (s s' : State) (ℓ : Label), lp.relevant s → lp.behavior s ℓ s' →
        projectedOracle lp.oracle lp.observe X ℓ
          (project lp.observe X s) (project lp.observe X s')) ∧
      -- Controllable: same projection → same behavior availability
      (∀ (s₁ s₂ : State) (ℓ : Label), lp.relevant s₁ →
        project lp.observe X s₁ = project lp.observe X s₂ →
        (∃ s₁', lp.behavior s₁ ℓ s₁') →
        (∃ s₂', lp.behavior s₂ ℓ s₂')) ∧
      -- Injective: same projection on relevant states → equal
      (∀ (s₁ s₂ : State), lp.relevant s₁ → lp.relevant s₂ →
        project lp.observe X s₁ = project lp.observe X s₂ → s₁ = s₂) := by
  -- Combined refinement: non-controllability disagreements ∪ relevant-state disagreements
  let refStep : Finset Dim → Finset Dim := fun X =>
    X ∪ Finset.univ.filter (fun d =>
      -- Non-controllability disagreements (same as extraction_exists)
      (∃ (s₁ s₂ : State) (ℓ : Label),
        lp.relevant s₁ ∧
        (∃ s₁', lp.behavior s₁ ℓ s₁') ∧
        project lp.observe X s₂ = project lp.observe X s₁ ∧
        (¬∃ s₂', lp.behavior s₂ ℓ s₂') ∧
        lp.observe s₁ d ≠ lp.observe s₂ d) ∨
      -- Relevant-state observation disagreements
      (∃ (s₁ s₂ : State),
        lp.relevant s₁ ∧ lp.relevant s₂ ∧
        project lp.observe X s₁ = project lp.observe X s₂ ∧
        lp.observe s₁ d ≠ lp.observe s₂ d))
  have h_infl : ∀ X, X ⊆ refStep X := fun _ => Finset.subset_union_left
  obtain ⟨n, h_conv⟩ := inflationary_stabilizes refStep h_infl ∅
  let X := refStep^[n] ∅
  have h_fp : refStep X = X := by
    show refStep (refStep^[n] ∅) = refStep^[n] ∅
    have : refStep^[n + 1] ∅ = refStep^[n] ∅ := h_conv
    rwa [Function.iterate_succ_apply'] at this
  -- Key: relevant-state injectivity at fixpoint
  have h_inj : ∀ (s₁ s₂ : State),
      lp.relevant s₁ → lp.relevant s₂ →
      project lp.observe X s₁ = project lp.observe X s₂ → s₁ = s₂ := by
    intro s₁ s₂ hr₁ hr₂ hπ
    apply lp.identifiable s₁ s₂ hr₁
    intro d
    by_cases hd : d ∈ X
    · have h_pe : (if d ∈ X then lp.observe s₁ d else (default : Value)) =
          (if d ∈ X then lp.observe s₂ d else default) := congr_fun hπ d
      rw [if_pos hd, if_pos hd] at h_pe
      exact h_pe
    · by_contra hne
      have h_mem : d ∈ refStep X := Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ d,
          Or.inr ⟨s₁, s₂, hr₁, hr₂, hπ, hne⟩⟩)
      rw [h_fp] at h_mem
      exact hd h_mem
  refine ⟨X, ?_, ?_, h_inj⟩
  -- Soundness: from oracle soundness
  · intro s s' ℓ hr hbeh
    exact ⟨s, s', rfl, lp.sound s s' ℓ hbeh, rfl⟩
  -- Controllability: at fixpoint, identifiability makes it vacuous
  · intro s₁ s₂ ℓ hr₁ hπ ⟨s₁', hbeh⟩
    by_cases h_can : ∃ s', lp.behavior s₂ ℓ s'
    · exact h_can
    · exfalso; apply h_can
      have h_eq : s₁ = s₂ := by
        apply lp.identifiable _ _ hr₁
        intro d
        by_cases hd : d ∈ X
        · have h_pe : (if d ∈ X then lp.observe s₁ d else (default : Value)) =
              (if d ∈ X then lp.observe s₂ d else default) := congr_fun hπ d
          rw [if_pos hd, if_pos hd] at h_pe
          exact h_pe
        · by_contra h_ne
          have h_mem : d ∈ refStep X := Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ d,
              Or.inl ⟨s₁, s₂, ℓ, hr₁, ⟨s₁', hbeh⟩,
                hπ.symm, h_can, h_ne⟩⟩)
          rw [h_fp] at h_mem
          exact hd h_mem
      subst h_eq; exact ⟨s₁', hbeh⟩

/-! ## Relevance-Restricted Oracle

The unrestricted `projectedOracle` existentially quantifies over ALL states
as witnesses. For reverse bisimulation, the witness must be relevant so that
injectivity (which holds only on relevant states) can identify it with the
query state. `relevantProjectedOracle` restricts the first witness to
relevant states. -/

/-- Projected oracle restricted to relevant first witnesses. -/
abbrev relevantProjectedOracle {State Label Dim Value : Type*}
    [DecidableEq Dim] [Inhabited Value]
    (relevant : State → Prop)
    (oracle : Label → State → State → Prop)
    (observe : State → Dim → Value) (X : Finset Dim)
    : Label → (Dim → Value) → (Dim → Value) → Prop :=
  fun ℓ x x' => ∃ s s', relevant s ∧ project observe X s = x ∧
    oracle ℓ s s' ∧ project observe X s' = x'

/-- The relevance-restricted oracle is sound: every behavior of a relevant
    state is witnessed by that state itself. -/
theorem LearnabilityPreconditions.relevantProjectedOracle_sound
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value)
    (X : Finset Dim) :
    ∀ (s s' : State) (ℓ : Label), lp.relevant s → lp.behavior s ℓ s' →
      relevantProjectedOracle lp.relevant lp.oracle lp.observe X ℓ
        (project lp.observe X s) (project lp.observe X s') :=
  fun s s' ℓ hr hbeh => ⟨s, s', hr, rfl, lp.sound s s' ℓ hbeh, rfl⟩

open Classical in
/-- At an injectivity fixpoint, a relevance-restricted oracle claim by a
    relevant state can be "de-projected": the existential witness equals
    the query state, so completeness gives real behavior.

    This is the key theorem for reverse bisimulation: if the projected
    oracle claims `R(ℓ, π(s), x')` with a relevant witness, and the
    projection is injective on relevant states, then `s` itself has
    real behavior producing a state that projects to `x'`.

    This is the first theorem that uses `complete`. -/
theorem LearnabilityPreconditionsComplete.relevantProjectedOracle_witness_eq
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    {X : Finset Dim} {s : State} {ℓ : Label} {x' : Dim → Value}
    (h_inj : ∀ (s₁ s₂ : State), lp.relevant s₁ → lp.relevant s₂ →
      project lp.observe X s₁ = project lp.observe X s₂ → s₁ = s₂)
    (hr : lp.relevant s)
    (hclaim : relevantProjectedOracle lp.relevant lp.oracle lp.observe X ℓ
      (project lp.observe X s) x') :
    ∃ s', lp.behavior s ℓ s' ∧ project lp.observe X s' = x' := by
  obtain ⟨s₀, s₀', hr₀, hπ₀, horac, hπ₀'⟩ := hclaim
  have h_eq : s₀ = s := h_inj s₀ s hr₀ hr hπ₀
  subst h_eq
  exact ⟨s₀', lp.complete _ s₀' ℓ horac, hπ₀'⟩

/-! ## Strengthened Extraction: Named Constructions

The theorems above use existentials (`∃ X, ...`), which are trivially
satisfiable by `X = Finset.univ` given `identifiable`. The definitions and
theorems below make the refinement construction explicit: the dimension
set is a named `def`, and every tracked dimension carries a concrete
certificate of necessity.

This captures the actual content: the refinement algorithm discovers
which dimensions matter, starting from nothing. -/

-- Helper: extract observation equality from projection equality at a tracked dim
private theorem obs_eq_of_proj_eq_mem
    {State Dim Value : Type*}
    [DecidableEq Dim] [Inhabited Value]
    {observe : State → Dim → Value} {X : Finset Dim}
    {s₁ s₂ : State} {d : Dim}
    (hproj : project observe X s₁ = project observe X s₂)
    (hd : d ∈ X) : observe s₁ d = observe s₂ d := by
  have h_pe : (if d ∈ X then observe s₁ d else (default : Value)) =
      (if d ∈ X then observe s₂ d else default) := congr_fun hproj d
  rw [if_pos hd, if_pos hd] at h_pe
  exact h_pe

/-! ### Sound-only case (simulation) -/

open Classical in
/-- The number of refinement steps needed to reach fixpoint. -/
noncomputable def LearnabilityPreconditions.refinementSteps
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value) : ℕ :=
  (inflationary_stabilizes (refineStep lp.toObservableSystem)
    (fun X => Finset.subset_union_left) ∅).choose

open Classical in
/-- The fixpoint dimension set discovered by refinement from ∅.
    This is THE specific set the algorithm produces — not "some set
    that happens to work." -/
noncomputable def LearnabilityPreconditions.extractionDims
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value) : Finset Dim :=
  (refineStep lp.toObservableSystem)^[lp.refinementSteps] ∅

open Classical in
/-- extractionDims is a fixpoint of refineStep. This is the concrete
    witness for the existential in `extraction_exists` — the named dimension
    set at which refinement stabilizes. -/
theorem LearnabilityPreconditions.extractionDims_is_fixpoint
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value) :
    refineStep lp.toObservableSystem lp.extractionDims = lp.extractionDims := by
  let f := refineStep lp.toObservableSystem
  let h_infl : ∀ X, X ⊆ f X := fun X => Finset.subset_union_left
  have h : f^[lp.refinementSteps + 1] ∅ = f^[lp.refinementSteps] ∅ :=
    (inflationary_stabilizes f h_infl ∅).choose_spec
  show f (f^[lp.refinementSteps] ∅) = f^[lp.refinementSteps] ∅
  rw [Function.iterate_succ_apply'] at h
  exact h

open Classical in
/-- Extraction is tractable: `refineStep` reaches a fixpoint in at most
    `Fintype.card Dim` iterations starting from ∅.

    This is `inflationary_stabilizes_bound` specialized to the learnability
    setting. `refineStep` is inflationary (only adds dimensions), so the chain
    of dimension sets strictly increases at each non-fixpoint step, bounded
    by |Dim| total elements.

    Finding *a* faithful fixpoint is tractable (this theorem). Finding the
    *minimum* faithful fixpoint is NP-hard (Jha & Seshia 2018, Theorem 6.1). -/
theorem LearnabilityPreconditions.extraction_cost_bound
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value) :
    ∃ n, n ≤ Fintype.card Dim ∧
      (refineStep lp.toObservableSystem)^[n + 1] ∅ =
      (refineStep lp.toObservableSystem)^[n] ∅ :=
  inflationary_stabilizes_bound _ (fun _ => Finset.subset_union_left) ∅

open Classical in
/-- The extracted dimensions are sound: every behavior of a relevant
    state is captured by the projected oracle through extractionDims.
    This is the first half of `extraction_exists`, instantiated at the
    named fixpoint `extractionDims`. -/
theorem LearnabilityPreconditions.extractionDims_sound
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value) :
    ∀ (s s' : State) (ℓ : Label), lp.relevant s → lp.behavior s ℓ s' →
      projectedOracle lp.oracle lp.observe lp.extractionDims ℓ
        (project lp.observe lp.extractionDims s)
        (project lp.observe lp.extractionDims s') := by
  intro s s' ℓ _hr hbeh
  exact ⟨s, s', rfl, lp.sound s s' ℓ hbeh, rfl⟩

open Classical in
/-- The extracted dimensions are controllable: states with the same
    projection have the same behavior availability. This is the second
    half of `extraction_exists`, instantiated at the named fixpoint
    `extractionDims`. -/
theorem LearnabilityPreconditions.extractionDims_controllable
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value) :
    ∀ (s₁ s₂ : State) (ℓ : Label), lp.relevant s₁ →
      project lp.observe lp.extractionDims s₁ =
        project lp.observe lp.extractionDims s₂ →
      (∃ s₁', lp.behavior s₁ ℓ s₁') →
      (∃ s₂', lp.behavior s₂ ℓ s₂') := by
  intro s₁ s₂ ℓ h_rel hproj_eq ⟨s₁', hbeh⟩
  have h_fp := lp.extractionDims_is_fixpoint
  by_cases h_can : ∃ s', lp.behavior s₂ ℓ s'
  · exact h_can
  · exfalso; apply h_can
    have h_eq : s₁ = s₂ := by
      apply lp.identifiable _ _ h_rel
      intro d
      by_cases hd : d ∈ lp.extractionDims
      · exact obs_eq_of_proj_eq_mem hproj_eq hd
      · by_contra h_ne
        have h_mem : d ∈ refineStep lp.toObservableSystem lp.extractionDims := by
          apply Finset.mem_union_right
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ d, s₁, s₂, ℓ, h_rel, ⟨s₁', hbeh⟩,
                 hproj_eq.symm, h_can, h_ne⟩
        rw [h_fp] at h_mem
        exact hd h_mem
    subst h_eq; exact ⟨s₁', hbeh⟩

open Classical in
/-- Every dimension in extractionDims entered at a specific refinement
    step — it wasn't tracked before that step, and was added by it. -/
theorem LearnabilityPreconditions.extractionDims_each_dim_justified
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value)
    (d : Dim) (hd : d ∈ lp.extractionDims) :
    ∃ k, d ∉ (refineStep lp.toObservableSystem)^[k] ∅ ∧
      d ∈ (refineStep lp.toObservableSystem)^[k + 1] ∅ := by
  unfold LearnabilityPreconditions.extractionDims at hd
  by_contra h_none
  push_neg at h_none
  have h_never : ∀ k, d ∉ (refineStep lp.toObservableSystem)^[k] ∅ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact h_none k ih
  exact absurd hd (h_never _)

open Classical in
/-- Full certificate: every dimension in extractionDims has concrete
    witnesses — states s₁, s₂ and label ℓ — that CAUSED it to be added.
    At the refinement step k where d entered:
    - s₁ is relevant and can take ℓ (to some s₁')
    - s₂ has the same projection as s₁ at step k but CANNOT take ℓ
    - s₁ and s₂ disagree at dimension d

    This is the "certificate of necessity" for each tracked dimension.
    `Finset.univ` cannot satisfy this — dimensions that witness no
    disagreement have no such certificate. -/
theorem LearnabilityPreconditions.extractionDims_each_dim_witnessed
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value)
    (d : Dim) (hd : d ∈ lp.extractionDims) :
    ∃ (k : ℕ) (s₁ s₂ : State) (ℓ : Label),
      let Xk := (refineStep lp.toObservableSystem)^[k] ∅
      d ∉ Xk ∧
      lp.relevant s₁ ∧
      (∃ s₁', lp.behavior s₁ ℓ s₁') ∧
      project lp.observe Xk s₂ = project lp.observe Xk s₁ ∧
      (¬∃ s₂', lp.behavior s₂ ℓ s₂') ∧
      lp.observe s₁ d ≠ lp.observe s₂ d := by
  obtain ⟨k, hk_out, hk_in⟩ := lp.extractionDims_each_dim_justified d hd
  set Xk := (refineStep lp.toObservableSystem)^[k] ∅ with hXk_def
  have hk_in' : d ∈ refineStep lp.toObservableSystem Xk := by
    have : (refineStep lp.toObservableSystem)^[k + 1] ∅ =
        refineStep lp.toObservableSystem ((refineStep lp.toObservableSystem)^[k] ∅) :=
      Function.iterate_succ_apply' _ k ∅
    rw [this] at hk_in; exact hk_in
  rw [Finset.mem_union] at hk_in'
  have h_in_filter : d ∈ Finset.univ.filter (fun d =>
    ∃ (s₁ s₂ : State) (ℓ : Label),
      lp.relevant s₁ ∧
      (∃ s₁', lp.behavior s₁ ℓ s₁') ∧
      project lp.observe Xk s₂ = project lp.observe Xk s₁ ∧
      (¬∃ s₂', lp.behavior s₂ ℓ s₂') ∧
      lp.observe s₁ d ≠ lp.observe s₂ d) := hk_in'.resolve_left hk_out
  rw [Finset.mem_filter] at h_in_filter
  obtain ⟨_, s₁, s₂, ℓ, h_rel, h_beh, h_proj, h_cant, h_ne⟩ := h_in_filter
  exact ⟨k, s₁, s₂, ℓ, hk_out, h_rel, h_beh, h_proj, h_cant, h_ne⟩

/-! ### Complete oracle case (bisimulation) -/

open Classical in
/-- Combined refinement step: non-controllability disagreements ∪
    relevant-state observation disagreements. The second disjunct
    ensures the fixpoint projection is injective on relevant states. -/
noncomputable abbrev refineStepComplete {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (sys : ObservableSystem State Label Dim Value) (X : Finset Dim)
    : Finset Dim :=
  X ∪ Finset.univ.filter (fun d =>
    (∃ (s₁ s₂ : State) (ℓ : Label),
      sys.relevant s₁ ∧
      (∃ s₁', sys.behavior s₁ ℓ s₁') ∧
      project sys.observe X s₂ = project sys.observe X s₁ ∧
      (¬∃ s₂', sys.behavior s₂ ℓ s₂') ∧
      sys.observe s₁ d ≠ sys.observe s₂ d) ∨
    (∃ (s₁ s₂ : State),
      sys.relevant s₁ ∧ sys.relevant s₂ ∧
      project sys.observe X s₁ = project sys.observe X s₂ ∧
      sys.observe s₁ d ≠ sys.observe s₂ d))

open Classical in
/-- Number of combined refinement steps to fixpoint. -/
noncomputable def LearnabilityPreconditionsComplete.refinementSteps
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) : ℕ :=
  (inflationary_stabilizes (refineStepComplete lp.toObservableSystem)
    (fun X => Finset.subset_union_left) ∅).choose

open Classical in
/-- The fixpoint dimension set from combined refinement. -/
noncomputable def LearnabilityPreconditionsComplete.extractionDims
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) : Finset Dim :=
  (refineStepComplete lp.toObservableSystem)^[lp.refinementSteps] ∅

open Classical in
/-- Combined refinement reaches a fixpoint. -/
theorem LearnabilityPreconditionsComplete.extractionDims_is_fixpoint
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    refineStepComplete lp.toObservableSystem lp.extractionDims =
      lp.extractionDims := by
  let f := refineStepComplete lp.toObservableSystem
  let h_infl : ∀ X, X ⊆ f X := fun X => Finset.subset_union_left
  have h : f^[lp.refinementSteps + 1] ∅ = f^[lp.refinementSteps] ∅ :=
    (inflationary_stabilizes f h_infl ∅).choose_spec
  show f (f^[lp.refinementSteps] ∅) = f^[lp.refinementSteps] ∅
  rw [Function.iterate_succ_apply'] at h
  exact h

open Classical in
/-- Extraction with complete oracle is tractable: `refineStepComplete` reaches
    a fixpoint in at most `Fintype.card Dim` iterations starting from ∅.
    Parallel to `LearnabilityPreconditions.extraction_cost_bound`. -/
theorem LearnabilityPreconditionsComplete.extraction_cost_bound
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    ∃ n, n ≤ Fintype.card Dim ∧
      (refineStepComplete lp.toObservableSystem)^[n + 1] ∅ =
      (refineStepComplete lp.toObservableSystem)^[n] ∅ :=
  inflationary_stabilizes_bound _ (fun _ => Finset.subset_union_left) ∅

open Classical in
/-- At the combined fixpoint, the projection is injective on relevant states. -/
theorem LearnabilityPreconditionsComplete.extractionDims_injective
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    ∀ (s₁ s₂ : State), lp.relevant s₁ → lp.relevant s₂ →
      project lp.observe lp.extractionDims s₁ =
        project lp.observe lp.extractionDims s₂ → s₁ = s₂ := by
  intro s₁ s₂ hr₁ hr₂ hπ
  have h_fp := lp.extractionDims_is_fixpoint
  apply lp.identifiable s₁ s₂ hr₁
  intro d
  by_cases hd : d ∈ lp.extractionDims
  · exact obs_eq_of_proj_eq_mem hπ hd
  · by_contra hne
    have h_mem : d ∈ refineStepComplete lp.toObservableSystem lp.extractionDims :=
      Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ d, Or.inr ⟨s₁, s₂, hr₁, hr₂, hπ, hne⟩⟩)
    rw [h_fp] at h_mem
    exact hd h_mem

open Classical in
/-- Sound at combined fixpoint. -/
theorem LearnabilityPreconditionsComplete.extractionDims_sound
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    ∀ (s s' : State) (ℓ : Label), lp.relevant s → lp.behavior s ℓ s' →
      projectedOracle lp.oracle lp.observe lp.extractionDims ℓ
        (project lp.observe lp.extractionDims s)
        (project lp.observe lp.extractionDims s') := by
  intro s s' ℓ _hr hbeh
  exact ⟨s, s', rfl, lp.sound s s' ℓ hbeh, rfl⟩

open Classical in
/-- Controllable at combined fixpoint. -/
theorem LearnabilityPreconditionsComplete.extractionDims_controllable
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    ∀ (s₁ s₂ : State) (ℓ : Label), lp.relevant s₁ →
      project lp.observe lp.extractionDims s₁ =
        project lp.observe lp.extractionDims s₂ →
      (∃ s₁', lp.behavior s₁ ℓ s₁') →
      (∃ s₂', lp.behavior s₂ ℓ s₂') := by
  intro s₁ s₂ ℓ h_rel hproj_eq ⟨s₁', hbeh⟩
  have h_fp := lp.extractionDims_is_fixpoint
  by_cases h_can : ∃ s', lp.behavior s₂ ℓ s'
  · exact h_can
  · exfalso; apply h_can
    have h_eq : s₁ = s₂ := by
      apply lp.identifiable _ _ h_rel
      intro d
      by_cases hd : d ∈ lp.extractionDims
      · exact obs_eq_of_proj_eq_mem hproj_eq hd
      · by_contra h_ne
        have h_mem : d ∈ refineStepComplete lp.toObservableSystem
            lp.extractionDims :=
          Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_univ d, Or.inl ⟨s₁, s₂, ℓ, h_rel, ⟨s₁', hbeh⟩,
              hproj_eq.symm, h_can, h_ne⟩⟩)
        rw [h_fp] at h_mem
        exact hd h_mem
    subst h_eq; exact ⟨s₁', hbeh⟩

open Classical in
/-- The relevance-restricted oracle is sound at the combined fixpoint. -/
theorem LearnabilityPreconditionsComplete.extractionDims_relevantOracle_sound
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    ∀ (s s' : State) (ℓ : Label), lp.relevant s → lp.behavior s ℓ s' →
      relevantProjectedOracle lp.relevant lp.oracle lp.observe
        lp.extractionDims ℓ
        (project lp.observe lp.extractionDims s)
        (project lp.observe lp.extractionDims s') :=
  fun s s' ℓ hr hbeh => ⟨s, s', hr, rfl, lp.sound s s' ℓ hbeh, rfl⟩

open Classical in
/-- Reverse direction: at the combined fixpoint, a relevance-restricted
    oracle claim can be "de-projected." If the projected oracle claims
    R(ℓ, π(s), x') with a relevant witness, then s itself has real
    behavior producing a state that projects to x'.

    Uses injectivity (the relevant witness must be s) and completeness
    (oracle claim → real behavior). This is the key lemma for reverse
    bisimulation. -/
theorem LearnabilityPreconditionsComplete.extractionDims_deproject
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    {s : State} {ℓ : Label} {x' : Dim → Value}
    (hr : lp.relevant s)
    (hclaim : relevantProjectedOracle lp.relevant lp.oracle lp.observe
      lp.extractionDims ℓ
      (project lp.observe lp.extractionDims s) x') :
    ∃ s', lp.behavior s ℓ s' ∧
      project lp.observe lp.extractionDims s' = x' := by
  obtain ⟨s₀, s₀', hr₀, hπ₀, horac, hπ₀'⟩ := hclaim
  have h_eq : s₀ = s := lp.extractionDims_injective s₀ s hr₀ hr hπ₀
  subst h_eq
  exact ⟨s₀', lp.complete _ s₀' ℓ horac, hπ₀'⟩

/-! ### Certificates of necessity (complete case) -/

open Classical in
/-- Every dimension in extractionDims entered at a specific step. -/
theorem LearnabilityPreconditionsComplete.extractionDims_each_dim_justified
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (d : Dim) (hd : d ∈ lp.extractionDims) :
    ∃ k, d ∉ (refineStepComplete lp.toObservableSystem)^[k] ∅ ∧
      d ∈ (refineStepComplete lp.toObservableSystem)^[k + 1] ∅ := by
  unfold LearnabilityPreconditionsComplete.extractionDims at hd
  by_contra h_none
  push_neg at h_none
  have h_never : ∀ k, d ∉ (refineStepComplete lp.toObservableSystem)^[k] ∅ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact h_none k ih
  exact absurd hd (h_never _)

open Classical in
/-- Full certificate: every dimension in the complete extractionDims was
    added because it witnessed EITHER a non-controllability disagreement
    OR a relevant-state observation disagreement. The disjunction in the
    conclusion mirrors the disjunction in refineStepComplete's filter. -/
theorem LearnabilityPreconditionsComplete.extractionDims_each_dim_witnessed
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (d : Dim) (hd : d ∈ lp.extractionDims) :
    ∃ (k : ℕ),
      let Xk := (refineStepComplete lp.toObservableSystem)^[k] ∅
      d ∉ Xk ∧
      ((∃ (s₁ s₂ : State) (ℓ : Label),
          lp.relevant s₁ ∧
          (∃ s₁', lp.behavior s₁ ℓ s₁') ∧
          project lp.observe Xk s₂ = project lp.observe Xk s₁ ∧
          (¬∃ s₂', lp.behavior s₂ ℓ s₂') ∧
          lp.observe s₁ d ≠ lp.observe s₂ d) ∨
       (∃ (s₁ s₂ : State),
          lp.relevant s₁ ∧ lp.relevant s₂ ∧
          project lp.observe Xk s₁ = project lp.observe Xk s₂ ∧
          lp.observe s₁ d ≠ lp.observe s₂ d)) := by
  obtain ⟨k, hk_out, hk_in⟩ := lp.extractionDims_each_dim_justified d hd
  set Xk := (refineStepComplete lp.toObservableSystem)^[k] ∅
  have hk_in' : d ∈ refineStepComplete lp.toObservableSystem Xk := by
    have : (refineStepComplete lp.toObservableSystem)^[k + 1] ∅ =
        refineStepComplete lp.toObservableSystem
          ((refineStepComplete lp.toObservableSystem)^[k] ∅) :=
      Function.iterate_succ_apply' _ k ∅
    rw [this] at hk_in; exact hk_in
  rw [Finset.mem_union] at hk_in'
  have h_in_filter := hk_in'.resolve_left hk_out
  rw [Finset.mem_filter] at h_in_filter
  exact ⟨k, hk_out, h_in_filter.2⟩

/-! ## Extraction at Arbitrary Fixpoints

`extraction_exists` proves properties at the specific fixpoint discovered by
iterating `refineStep` from `∅`. But its proof only uses the fixpoint property
`refineStep X = X`, not how X was constructed. This factored version works for
ANY fixpoint. -/

open Classical in
/-- Extraction at any fixpoint of `refineStep`.

    `extraction_exists` is the special case where `X = extractionDims`
    (the fixpoint discovered by iteration). Any other construction that
    produces a fixpoint gets the same soundness and controllability. -/
theorem LearnabilityPreconditions.extraction_at_fixpoint
    {State Label Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (lp : LearnabilityPreconditions State Label Dim Value)
    (X : Finset Dim)
    (h_fp : refineStep lp.toObservableSystem X = X) :
    (∀ (s s' : State) (ℓ : Label), lp.relevant s → lp.behavior s ℓ s' →
      projectedOracle lp.oracle lp.observe X ℓ
        (project lp.observe X s) (project lp.observe X s')) ∧
    (∀ (s₁ s₂ : State) (ℓ : Label), lp.relevant s₁ →
      project lp.observe X s₁ = project lp.observe X s₂ →
      (∃ s₁', lp.behavior s₁ ℓ s₁') →
      (∃ s₂', lp.behavior s₂ ℓ s₂')) := by
  refine ⟨?_, ?_⟩
  · intro s s' ℓ _hrel hbeh
    exact ⟨s, s', rfl, lp.sound s s' ℓ hbeh, rfl⟩
  · intro s₁ s₂ ℓ h_rel hproj_eq ⟨s₁', hbeh⟩
    by_cases h_can : ∃ s', lp.behavior s₂ ℓ s'
    · exact h_can
    · exfalso; apply h_can
      have h_eq : s₁ = s₂ := by
        apply lp.identifiable _ _ h_rel
        intro d
        by_cases hd : d ∈ X
        · exact obs_eq_of_proj_eq_mem hproj_eq hd
        · by_contra h_ne
          have h_mem : d ∈ refineStep lp.toObservableSystem X := by
            apply Finset.mem_union_right
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ d, s₁, s₂, ℓ, h_rel, ⟨s₁', hbeh⟩,
                   hproj_eq.symm, h_can, h_ne⟩
          rw [h_fp] at h_mem
          exact hd h_mem
      subst h_eq; exact ⟨s₁', hbeh⟩
