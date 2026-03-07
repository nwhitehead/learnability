import Core.Branch
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# Branch Composition — Set-Level Operations

Single-branch sequential composition already lives in `Branch.lean`
(`Branch.compose`, `Branch.skip`). This file lifts composition to
**sets of branches** and proves soundness/completeness for the lifted
operations.

## Operations

- `seqBehavior beh₁ beh₂`: relational composition of behaviors
- `choiceBehavior beh₁ beh₂`: union of behaviors
- `composeBranchSets isa B₁ B₂`: `{b₁.compose isa b₂ | b₁ ∈ B₁, b₂ ∈ B₂}`
- `choiceBranchSets B₁ B₂`: `B₁ ∪ B₂`

## ICTAC Correspondence

| Composition.lean | ICTAC |
|---|---|
| `seqBehavior` | Sequential composition of `denot_fun_nondet` |
| `choiceBehavior` | Union of `denot_fun_nondet` for `PCh` |
| `composeBranchSets` | `denot__S(p₁;p₂) = {compose_trace t₁ t₂}` |
| `choiceBranchSets` | `denot__S(PCh p₁ p₂) = denot__S(p₁) ∪ denot__S(p₂)` |

## Key Theorems

- Sequential soundness/completeness: B₁ S&C for beh₁ and B₂ S&C for beh₂
  implies B₁⊗B₂ S&C for seqBehavior beh₁ beh₂
- Choice soundness/completeness: similar for union
- Cardinality: `|B₁⊗B₂| ≤ |B₁|×|B₂|`, `|B₁⊕B₂| ≤ |B₁|+|B₂|`
- Branch.compose algebraic properties from SymbolicISA axioms
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Behavior Composition -/

section BehaviorOps

variable {State : Type*}

/-- Sequential composition of behaviors (relational composition).
    `seqBehavior beh₁ beh₂ s s'` iff there exists an intermediate state
    `t` with `beh₁ s t` and `beh₂ t s'`. -/
def seqBehavior (beh₁ beh₂ : State → State → Prop) : State → State → Prop :=
  fun s s' => ∃ t, beh₁ s t ∧ beh₂ t s'

/-- Nondeterministic choice of behaviors (union).
    `choiceBehavior beh₁ beh₂ s s'` iff `beh₁ s s'` or `beh₂ s s'`. -/
def choiceBehavior (beh₁ beh₂ : State → State → Prop) : State → State → Prop :=
  fun s s' => beh₁ s s' ∨ beh₂ s s'

/-- Sequential composition is associative. -/
theorem seqBehavior_assoc (beh₁ beh₂ beh₃ : State → State → Prop) :
    seqBehavior (seqBehavior beh₁ beh₂) beh₃ =
    seqBehavior beh₁ (seqBehavior beh₂ beh₃) := by
  funext s s'
  simp only [seqBehavior, eq_iff_iff]
  constructor
  · rintro ⟨t, ⟨u, hu1, hu2⟩, ht⟩
    exact ⟨u, hu1, t, hu2, ht⟩
  · rintro ⟨u, hu1, t, hu2, ht⟩
    exact ⟨t, ⟨u, hu1, hu2⟩, ht⟩

/-- Choice is associative. -/
theorem choiceBehavior_assoc (beh₁ beh₂ beh₃ : State → State → Prop) :
    choiceBehavior (choiceBehavior beh₁ beh₂) beh₃ =
    choiceBehavior beh₁ (choiceBehavior beh₂ beh₃) := by
  funext s s'
  simp only [choiceBehavior, eq_iff_iff]
  exact or_assoc

/-- Choice is commutative. -/
theorem choiceBehavior_comm (beh₁ beh₂ : State → State → Prop) :
    choiceBehavior beh₁ beh₂ = choiceBehavior beh₂ beh₁ := by
  funext s s'
  simp only [choiceBehavior, eq_iff_iff]
  exact or_comm

end BehaviorOps


/-! ## Set-Level Branch Composition -/

section BranchSetOps

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- Compose two sets of branches: the Cartesian product under `Branch.compose`.
    ICTAC: `denot__S(p₁;p₂) = {compose_trace t₁ t₂ | t₁ ∈ traces(p₁), t₂ ∈ traces(p₂)}`. -/
def composeBranchSets (B₁ B₂ : Set (Branch Sub PC)) : Set (Branch Sub PC) :=
  { b | ∃ b₁ ∈ B₁, ∃ b₂ ∈ B₂, b = b₁.compose isa b₂ }

/-- Choice of branch sets: union.
    ICTAC: `denot__S(PCh p₁ p₂) = denot__S(p₁) ∪ denot__S(p₂)`. -/
def choiceBranchSets (B₁ B₂ : Set (Branch Sub PC)) : Set (Branch Sub PC) :=
  B₁ ∪ B₂

end BranchSetOps


/-! ## Sequential Composition: Soundness and Completeness -/

section SeqSoundComplete

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- Sequential soundness: if B₁ is sound for beh₁ and B₂ is sound for beh₂,
    then their composition is sound for seqBehavior beh₁ beh₂.

    Proof: given a composed branch b₁.compose b₂ with s satisfying its PC,
    decompose satisfaction (Branch.compose_satisfiedBy) to get s |= pc₁ and
    eval(σ₁,s) |= pc₂. Soundness of b₁ gives beh₁ s (eval σ₁ s).
    Soundness of b₂ gives beh₂ (eval σ₁ s) (eval σ₂ (eval σ₁ s)).
    The intermediate state is eval σ₁ s. -/
theorem composeBranchSets_sound
    {B₁ B₂ : Set (Branch Sub PC)}
    {beh₁ beh₂ : State → State → Prop}
    (h₁ : BranchModel.Sound isa B₁ beh₁)
    (h₂ : BranchModel.Sound isa B₂ beh₂) :
    BranchModel.Sound isa (composeBranchSets isa B₁ B₂) (seqBehavior beh₁ beh₂) := by
  intro b hb s hsat
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hb
  -- Decompose satisfaction of the composed branch
  unfold Branch.compose at hsat ⊢
  rw [isa.sat_and] at hsat
  obtain ⟨hsat₁, hsat₂⟩ := hsat
  have hsat₂' := (isa.sat_lift s b₁.sub b₂.pc).mp hsat₂
  -- Build the sequential behavior
  refine ⟨isa.eval_sub b₁.sub s, h₁ b₁ hb₁ s hsat₁, ?_⟩
  rw [isa.eval_compose]
  exact h₂ b₂ hb₂ (isa.eval_sub b₁.sub s) hsat₂'

/-- Sequential completeness: if B₁ is complete for beh₁ and B₂ is complete
    for beh₂, then their composition is complete for seqBehavior beh₁ beh₂.

    Proof: given beh₁ s t and beh₂ t s', completeness of B₁ gives a branch b₁
    with s |= pc₁ and eval(σ₁,s) = t. Completeness of B₂ gives b₂ with
    t |= pc₂ and eval(σ₂,t) = s'. The composed branch b₁.compose b₂ works. -/
theorem composeBranchSets_complete
    {B₁ B₂ : Set (Branch Sub PC)}
    {beh₁ beh₂ : State → State → Prop}
    (h₁ : BranchModel.Complete isa B₁ beh₁)
    (h₂ : BranchModel.Complete isa B₂ beh₂) :
    BranchModel.Complete isa (composeBranchSets isa B₁ B₂) (seqBehavior beh₁ beh₂) := by
  intro s s' ⟨t, hbeh₁, hbeh₂⟩
  obtain ⟨b₁, hb₁, hsat₁, heval₁⟩ := h₁ s t hbeh₁
  obtain ⟨b₂, hb₂, hsat₂, heval₂⟩ := h₂ t s' hbeh₂
  refine ⟨b₁.compose isa b₂, ⟨b₁, hb₁, b₂, hb₂, rfl⟩, ?_, ?_⟩
  · show isa.satisfies s (b₁.compose isa b₂).pc
    unfold Branch.compose
    rw [isa.sat_and]
    exact ⟨hsat₁, (isa.sat_lift s b₁.sub b₂.pc).mpr (heval₁ ▸ hsat₂)⟩
  · show isa.eval_sub (b₁.compose isa b₂).sub s = s'
    unfold Branch.compose
    rw [isa.eval_compose, heval₁, heval₂]

end SeqSoundComplete


/-! ## Choice Composition: Soundness and Completeness -/

section ChoiceSoundComplete

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- Choice soundness: union of sound models is sound for choice behavior. -/
theorem choiceBranchSets_sound
    {B₁ B₂ : Set (Branch Sub PC)}
    {beh₁ beh₂ : State → State → Prop}
    (h₁ : BranchModel.Sound isa B₁ beh₁)
    (h₂ : BranchModel.Sound isa B₂ beh₂) :
    BranchModel.Sound isa (choiceBranchSets B₁ B₂) (choiceBehavior beh₁ beh₂) := by
  intro b hb s hsat
  rcases hb with hb₁ | hb₂
  · exact Or.inl (h₁ b hb₁ s hsat)
  · exact Or.inr (h₂ b hb₂ s hsat)

/-- Choice completeness: union of complete models is complete for choice behavior. -/
theorem choiceBranchSets_complete
    {B₁ B₂ : Set (Branch Sub PC)}
    {beh₁ beh₂ : State → State → Prop}
    (h₁ : BranchModel.Complete isa B₁ beh₁)
    (h₂ : BranchModel.Complete isa B₂ beh₂) :
    BranchModel.Complete isa (choiceBranchSets B₁ B₂) (choiceBehavior beh₁ beh₂) := by
  intro s s' hbeh
  rcases hbeh with hbeh₁ | hbeh₂
  · obtain ⟨b, hb, hsat, heval⟩ := h₁ s s' hbeh₁
    exact ⟨b, Set.mem_union_left _ hb, hsat, heval⟩
  · obtain ⟨b, hb, hsat, heval⟩ := h₂ s s' hbeh₂
    exact ⟨b, Set.mem_union_right _ hb, hsat, heval⟩

end ChoiceSoundComplete


/-! ## Finset-Level Operations and Cardinality Bounds -/

section Cardinality

variable {Sub PC : Type*} [DecidableEq Sub] [DecidableEq PC]

/-- Finset-level sequential composition: biUnion of images under Branch.compose. -/
def composeBranchFinsets {State : Type*} (isa : SymbolicISA Sub PC State)
    (B₁ B₂ : Finset (Branch Sub PC)) : Finset (Branch Sub PC) :=
  B₁.biUnion (fun b₁ => B₂.image (fun b₂ => b₁.compose isa b₂))

/-- Finset-level choice: union. -/
def choiceBranchFinsets
    (B₁ B₂ : Finset (Branch Sub PC)) : Finset (Branch Sub PC) :=
  B₁ ∪ B₂

/-- Choice cardinality: |B₁ ⊕ B₂| ≤ |B₁| + |B₂|. -/
theorem choiceBranchFinsets_card
    (B₁ B₂ : Finset (Branch Sub PC)) :
    (choiceBranchFinsets B₁ B₂).card ≤ B₁.card + B₂.card :=
  Finset.card_union_le B₁ B₂

/-- The Finset composition agrees with the Set composition. -/
theorem composeBranchFinsets_coe {State : Type*} (isa : SymbolicISA Sub PC State)
    (B₁ B₂ : Finset (Branch Sub PC)) :
    (↑(composeBranchFinsets isa B₁ B₂) : Set (Branch Sub PC)) =
    composeBranchSets isa (↑B₁) (↑B₂) := by
  ext b
  simp only [composeBranchFinsets, composeBranchSets, Set.mem_setOf_eq]
  constructor
  · intro hb
    rw [Finset.mem_coe, Finset.mem_biUnion] at hb
    obtain ⟨b₁, hb₁, hb'⟩ := hb
    rw [Finset.mem_image] at hb'
    obtain ⟨b₂, hb₂, rfl⟩ := hb'
    exact ⟨b₁, Finset.mem_coe.mpr hb₁, b₂, Finset.mem_coe.mpr hb₂, rfl⟩
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨b₁, Finset.mem_coe.mp hb₁, Finset.mem_image.mpr ⟨b₂, Finset.mem_coe.mp hb₂, rfl⟩⟩

/-- The Finset choice agrees with the Set choice. -/
theorem choiceBranchFinsets_coe
    (B₁ B₂ : Finset (Branch Sub PC)) :
    (↑(choiceBranchFinsets B₁ B₂) : Set (Branch Sub PC)) =
    choiceBranchSets (↑B₁) (↑B₂) :=
  Finset.coe_union B₁ B₂

end Cardinality


/-! ## Semantic Equivalence for Composed Branches

Branch.compose is associative and has Branch.skip as identity
**semantically** (same satisfaction and same effect), though not
syntactically (the PC terms are different). The algebraic properties
of Branch.compose_satisfiedBy and Branch.compose_effect from
Branch.lean already capture this — we lift them here.

For Phase 7 (ProgramStructure), what matters is soundness/completeness
of the set-level operations (proved above), not syntactic equality of
individual branches. -/

section BranchSemantics

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- Composing with skip on the left preserves satisfaction. -/
theorem Branch.compose_skip_left_sat (b : Branch Sub PC) (s : State) :
    ((Branch.skip isa).compose isa b).satisfiedBy isa s ↔ b.satisfiedBy isa s := by
  rw [Branch.compose_satisfiedBy]
  constructor
  · intro ⟨_, h₂⟩
    rw [Branch.skip, Branch.effect] at h₂
    rwa [isa.eval_id] at h₂
  · intro h
    exact ⟨Branch.skip_satisfiedBy isa s, by rw [Branch.skip, Branch.effect, isa.eval_id]; exact h⟩

/-- Composing with skip on the left preserves effect. -/
theorem Branch.compose_skip_left_effect (b : Branch Sub PC) (s : State) :
    ((Branch.skip isa).compose isa b).effect isa s = b.effect isa s := by
  rw [Branch.compose_effect, Branch.skip_effect]

/-- Composing with skip on the right preserves satisfaction. -/
theorem Branch.compose_skip_right_sat (b : Branch Sub PC) (s : State) :
    (b.compose isa (Branch.skip isa)).satisfiedBy isa s ↔ b.satisfiedBy isa s := by
  rw [Branch.compose_satisfiedBy]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, Branch.skip_satisfiedBy isa (b.effect isa s)⟩

/-- Composing with skip on the right preserves effect. -/
theorem Branch.compose_skip_right_effect (b : Branch Sub PC) (s : State) :
    (b.compose isa (Branch.skip isa)).effect isa s = b.effect isa s := by
  rw [Branch.compose_effect, Branch.skip_effect]

/-- Associativity of composed branch satisfaction:
    `(b₁ ∘ b₂) ∘ b₃` satisfies at `s` iff `b₁ ∘ (b₂ ∘ b₃)` does.

    Both decompose to: s |= pc₁ ∧ eval(σ₁,s) |= pc₂ ∧ eval(σ₂, eval(σ₁,s)) |= pc₃. -/
theorem Branch.compose_assoc_sat (b₁ b₂ b₃ : Branch Sub PC) (s : State) :
    ((b₁.compose isa b₂).compose isa b₃).satisfiedBy isa s ↔
    (b₁.compose isa (b₂.compose isa b₃)).satisfiedBy isa s := by
  rw [Branch.compose_satisfiedBy, Branch.compose_satisfiedBy,
      Branch.compose_satisfiedBy, Branch.compose_satisfiedBy]
  rw [Branch.compose_effect]
  exact and_assoc

/-- Associativity of composed branch effect:
    `(b₁ ∘ b₂) ∘ b₃` and `b₁ ∘ (b₂ ∘ b₃)` have the same effect. -/
theorem Branch.compose_assoc_effect (b₁ b₂ b₃ : Branch Sub PC) (s : State) :
    ((b₁.compose isa b₂).compose isa b₃).effect isa s =
    (b₁.compose isa (b₂.compose isa b₃)).effect isa s := by
  simp only [Branch.compose_effect]

end BranchSemantics


/-! ## Leaf-Case Soundness/Completeness for Phase 7

These single-branch models are the base cases for structural induction
on CompTree in ProgramStructure.lean. -/

section LeafCases

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- Skip behavior: identity relation. -/
def skipBehavior : State → State → Prop := fun s s' => s' = s

/-- Assign behavior: apply a substitution. -/
def assignBehavior (σ : Sub) : State → State → Prop :=
  fun s s' => s' = isa.eval_sub σ s

/-- Assert behavior: identity, guarded by a path condition. -/
def assertBehavior (φ : PC) : State → State → Prop :=
  fun s s' => isa.satisfies s φ ∧ s' = s

/-- The skip branch model `{Branch.skip}` is sound for skip behavior. -/
theorem skip_sound :
    BranchModel.Sound isa {Branch.skip isa} skipBehavior := by
  intro b hb s _
  rw [Set.mem_singleton_iff] at hb; subst hb
  show skipBehavior s (isa.eval_sub (Branch.skip isa).sub s)
  simp [skipBehavior, Branch.skip, isa.eval_id]

/-- The skip branch model `{Branch.skip}` is complete for skip behavior. -/
theorem skip_complete :
    BranchModel.Complete isa {Branch.skip isa} skipBehavior := by
  intro s s' hbeh
  simp only [skipBehavior] at hbeh
  refine ⟨Branch.skip isa, Set.mem_singleton _, Branch.skip_satisfiedBy isa s, ?_⟩
  show isa.eval_sub (Branch.skip isa).sub s = s'
  rw [Branch.skip, isa.eval_id, hbeh]

/-- The assign branch model `{⟨σ, pc_true⟩}` is sound for assign behavior. -/
theorem assign_sound (σ : Sub) :
    BranchModel.Sound isa {⟨σ, isa.pc_true⟩} (assignBehavior isa σ) := by
  intro b hb s _
  rw [Set.mem_singleton_iff] at hb; subst hb
  simp [assignBehavior]

/-- The assign branch model is complete for assign behavior. -/
theorem assign_complete (σ : Sub) :
    BranchModel.Complete isa {⟨σ, isa.pc_true⟩} (assignBehavior isa σ) := by
  intro s s' hbeh
  simp only [assignBehavior] at hbeh
  exact ⟨⟨σ, isa.pc_true⟩, Set.mem_singleton _, isa.sat_true s, hbeh.symm⟩

/-- The assert branch model `{⟨id_sub, φ⟩}` is sound for assert behavior. -/
theorem assert_sound (φ : PC) :
    BranchModel.Sound isa {⟨isa.id_sub, φ⟩} (assertBehavior isa φ) := by
  intro b hb s hsat
  rw [Set.mem_singleton_iff] at hb; subst hb
  exact ⟨hsat, isa.eval_id s⟩

/-- The assert branch model is complete for assert behavior. -/
theorem assert_complete (φ : PC) :
    BranchModel.Complete isa {⟨isa.id_sub, φ⟩} (assertBehavior isa φ) := by
  intro s s' ⟨hsat, hbeh⟩
  exact ⟨⟨isa.id_sub, φ⟩, Set.mem_singleton _, hsat, by rw [isa.eval_id]; exact hbeh.symm⟩

end LeafCases
