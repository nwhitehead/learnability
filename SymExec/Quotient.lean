import SymExec.Bisimulation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
# Quotient Bisimulation

Extracts a finite abstract transition system from a complete branch model,
proved bisimilar to the concrete system. This is the publishable result of
Phase 4: "we extracted a finite abstract model."

## Construction

Given a sound and complete branch model `{b₁, ..., bₙ}`:

1. **PC closure**: close the model's PCs under `pc_lift bᵢ.sub (-)`.
   Semantically finite when `PC` is finite — bounded by `Fintype.card PC`.

2. **PC-equivalence**: `s ≈ s'` iff for all `φ ∈ PCClosure`,
   `satisfies s φ ↔ satisfies s' φ`.

3. **Congruence**: if `s ≈ s'` and branch b fires from s, then b fires
   from s' and successors are equivalent. Uses `sat_lift` + closure property.

4. **Abstract transitions**: defined existentially via representatives
   (avoiding `Quotient.lift₂`).

5. **Cross-system bisimulation**: quotient map is a bisimulation.

6. **Finiteness**: abstract states ≤ `2^|PCClosure|`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! ## Step 4a: PC Closure Construction

The PC closure is the smallest set containing all model PCs and closed
under `pc_lift bᵢ.sub (-)` for all branches in the model.

Computed by iterating `pcClosureStep` from `pcClosureBase` until fixpoint.
Terminates because `Finset PC` is bounded by `Finset.univ` when `[Fintype PC]`. -/

section PCClosure

variable {Sub PC State : Type*} [DecidableEq PC] [Fintype PC]
  (isa : SymbolicISA Sub PC State)

/-- One round of closure: add all lifts of current PCs through all branch subs. -/
def pcClosureStep (model : Finset (Branch Sub PC)) (current : Finset PC) : Finset PC :=
  current ∪ model.biUnion (fun b => current.image (isa.pc_lift b.sub))

/-- Starting set: the PCs appearing in the model. -/
def pcClosureBase (model : Finset (Branch Sub PC)) : Finset PC :=
  model.image (fun b => b.pc)

/-- Iterate closure step n times from the base. -/
def pcClosureSeq (model : Finset (Branch Sub PC)) (n : ℕ) : Finset PC :=
  (pcClosureStep isa model)^[n] (pcClosureBase model)

set_option linter.unusedSectionVars false in
/-- `pcClosureStep` is monotone: current ⊆ pcClosureStep current. -/
theorem pcClosureStep_mono (model : Finset (Branch Sub PC)) (current : Finset PC) :
    current ⊆ pcClosureStep isa model current :=
  Finset.subset_union_left

set_option linter.unusedSectionVars false in
/-- The closure sequence is monotone. -/
theorem pcClosureSeq_mono (model : Finset (Branch Sub PC)) :
    ∀ n, pcClosureSeq isa model n ⊆ pcClosureSeq isa model (n + 1) := by
  intro n
  show (pcClosureStep isa model)^[n] (pcClosureBase model) ⊆
       (pcClosureStep isa model)^[n + 1] (pcClosureBase model)
  rw [Function.iterate_succ_apply']
  exact pcClosureStep_mono isa model _

/-- The closure sequence is bounded by `Finset.univ`. -/
theorem pcClosureSeq_bounded (model : Finset (Branch Sub PC)) :
    ∀ n, pcClosureSeq isa model n ⊆ (Finset.univ : Finset PC) :=
  fun _ => Finset.subset_univ _

/-- The closure sequence stabilizes within `Fintype.card PC` steps. -/
theorem pcClosureSeq_stabilizes (model : Finset (Branch Sub PC)) :
    ∃ n, n ≤ (Finset.univ : Finset PC).card ∧
      pcClosureSeq isa model n = pcClosureSeq isa model (n + 1) :=
  Finset.bounded_monotone_stabilizes_within
    (pcClosureSeq isa model) (Finset.univ : Finset PC)
    (pcClosureSeq_mono isa model)
    (pcClosureSeq_bounded isa model)

/-- The PC closure: the fixpoint of `pcClosureStep` applied to model PCs. -/
noncomputable def pcClosure (model : Finset (Branch Sub PC)) : Finset PC :=
  pcClosureSeq isa model (pcClosureSeq_stabilizes isa model).choose

/-- The closure is a fixpoint of `pcClosureStep`. -/
theorem pcClosure_fixpoint (model : Finset (Branch Sub PC)) :
    pcClosureStep isa model (pcClosure isa model) = pcClosure isa model := by
  have h_fix := (pcClosureSeq_stabilizes isa model).choose_spec.2
  unfold pcClosure pcClosureSeq at h_fix ⊢
  rw [Function.iterate_succ_apply'] at h_fix
  exact h_fix.symm

/-- Closure property: for any branch in the model and any PC in the closure,
    the lifted PC is also in the closure. -/
theorem pcClosure_closed (model : Finset (Branch Sub PC))
    (b : Branch Sub PC) (hb : b ∈ model)
    (φ : PC) (hφ : φ ∈ pcClosure isa model) :
    isa.pc_lift b.sub φ ∈ pcClosure isa model := by
  have h_fix := pcClosure_fixpoint isa model
  rw [← h_fix]
  unfold pcClosureStep
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨b, hb, Finset.mem_image_of_mem _ hφ⟩

/-- The base PCs are contained in every step of the sequence. -/
theorem pcClosureBase_sub_seq (model : Finset (Branch Sub PC)) :
    ∀ n, pcClosureBase model ⊆ pcClosureSeq isa model n := by
  intro n
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact Finset.Subset.trans ih (pcClosureSeq_mono isa model n)

/-- The closure contains all model PCs. -/
theorem pcClosure_contains_model_pcs (model : Finset (Branch Sub PC))
    (b : Branch Sub PC) (hb : b ∈ model) :
    b.pc ∈ pcClosure isa model := by
  unfold pcClosure
  exact pcClosureBase_sub_seq isa model _ (Finset.mem_image_of_mem _ hb)

end PCClosure


/-! ## Step 4b: PC-Equivalence and Congruence

Two states are PC-equivalent (w.r.t. the closure) when they satisfy exactly
the same PCs in the closure. This is an equivalence relation, and it's a
congruence: transitions respect it.

The congruence proof uses `sat_lift` + the closure property from Step 4a. -/

section PCEquiv

variable {Sub PC State : Type*} [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Two states are PC-equivalent w.r.t. a closure: they agree on all PCs in it. -/
def pcEquiv (closure : Finset PC) (s₁ s₂ : State) : Prop :=
  ∀ φ ∈ closure, isa.satisfies s₁ φ ↔ isa.satisfies s₂ φ

set_option linter.unusedSectionVars false in
theorem pcEquiv_refl (closure : Finset PC) (s : State) :
    pcEquiv isa closure s s :=
  fun _ _ => Iff.rfl

set_option linter.unusedSectionVars false in
theorem pcEquiv_symm {closure : Finset PC} {s₁ s₂ : State}
    (h : pcEquiv isa closure s₁ s₂) : pcEquiv isa closure s₂ s₁ :=
  fun φ hφ => (h φ hφ).symm

set_option linter.unusedSectionVars false in
theorem pcEquiv_trans {closure : Finset PC} {s₁ s₂ s₃ : State}
    (h₁₂ : pcEquiv isa closure s₁ s₂) (h₂₃ : pcEquiv isa closure s₂ s₃) :
    pcEquiv isa closure s₁ s₃ :=
  fun φ hφ => (h₁₂ φ hφ).trans (h₂₃ φ hφ)

/-- PC-equivalence over an explicit closure as a `Setoid`. -/
def pcSetoidWith (closure : Finset PC) : Setoid State where
  r := pcEquiv isa closure
  iseqv := {
    refl := pcEquiv_refl isa _
    symm := pcEquiv_symm isa
    trans := pcEquiv_trans isa
  }

/-- If two states are PC-equivalent over an explicit closure and a branch PC lies in
    that closure, the branch fires from one state iff it fires from the other. -/
theorem pcEquiv_branch_firesWith {closure : Finset PC}
    {s₁ s₂ : State} {b : Branch Sub PC}
    (hb_mem : b.pc ∈ closure)
    (h_equiv : (pcSetoidWith isa closure).r s₁ s₂)
    (h_fires : isa.satisfies s₁ b.pc) :
    isa.satisfies s₂ b.pc :=
  (h_equiv b.pc hb_mem).mp h_fires

/-- If two states are PC-equivalent over an explicit closure and that closure is closed
    under lifting through branch `b`, their successors under `b` remain equivalent. -/
theorem pcEquiv_eval_subWith {closure : Finset PC}
    {s₁ s₂ : State} {b : Branch Sub PC}
    (hb_closed : ∀ φ ∈ closure, isa.pc_lift b.sub φ ∈ closure)
    (h_equiv : (pcSetoidWith isa closure).r s₁ s₂) :
    (pcSetoidWith isa closure).r (isa.eval_sub b.sub s₁) (isa.eval_sub b.sub s₂) := by
  intro φ hφ
  constructor
  · intro h
    rw [← isa.sat_lift s₂ b.sub φ]
    rw [← isa.sat_lift s₁ b.sub φ] at h
    exact (h_equiv (isa.pc_lift b.sub φ) (hb_closed φ hφ)).mp h
  · intro h
    rw [← isa.sat_lift s₁ b.sub φ]
    rw [← isa.sat_lift s₂ b.sub φ] at h
    exact (h_equiv (isa.pc_lift b.sub φ) (hb_closed φ hφ)).mpr h

variable [Fintype PC]

/-- PC-equivalence over a model's closure as a `Setoid`. -/
def pcSetoid (model : Finset (Branch Sub PC)) : Setoid State where
  r := (pcSetoidWith isa (pcClosure isa model)).r
  iseqv := (pcSetoidWith isa (pcClosure isa model)).iseqv

/-- If two states are PC-equivalent (over the closure) and a branch in the
    model fires from one, it fires from the other. -/
theorem pcEquiv_branch_fires {model : Finset (Branch Sub PC)}
    {s₁ s₂ : State} {b : Branch Sub PC}
    (hb : b ∈ model)
    (h_equiv : (pcSetoid isa model).r s₁ s₂)
    (h_fires : isa.satisfies s₁ b.pc) :
    isa.satisfies s₂ b.pc :=
  pcEquiv_branch_firesWith isa
    (pcClosure_contains_model_pcs isa model b hb) h_equiv h_fires

/-- If two states are PC-equivalent (over the closure), their successors
    under any branch in the model are also PC-equivalent.

    For any `φ ∈ closure`:
    `satisfies (eval_sub σ s₁) φ ↔ satisfies s₁ (pc_lift σ φ)` (by sat_lift)
    `↔ satisfies s₂ (pc_lift σ φ)` (by h_equiv, since pc_lift σ φ ∈ closure)
    `↔ satisfies (eval_sub σ s₂) φ` (by sat_lift). -/
theorem pcEquiv_eval_sub {model : Finset (Branch Sub PC)}
    {s₁ s₂ : State} {b : Branch Sub PC}
    (hb : b ∈ model)
    (h_equiv : (pcSetoid isa model).r s₁ s₂) :
    (pcSetoid isa model).r (isa.eval_sub b.sub s₁) (isa.eval_sub b.sub s₂) :=
  pcEquiv_eval_subWith isa
    (fun φ hφ => pcClosure_closed isa model b hb φ hφ) h_equiv

end PCEquiv


/-! ## Step 4c: Abstract Transitions and Cross-System Bisimulation

The abstract state space is the quotient of `State` by PC-equivalence.
Abstract transitions are defined existentially via representatives —
this avoids the `Quotient.lift₂` well-definedness obligation entirely.

The bisimulation proof shows the quotient map mediates between
concrete and abstract transitions. -/

section AbstractSystem

variable {Sub PC State : Type*} [DecidableEq PC] [Fintype PC]
  (isa : SymbolicISA Sub PC State)

/-- Abstract transition: `[s₁] →_abs [s₂]` iff some representatives
    are connected by a branch-induced transition. Defined existentially
    to avoid `Quotient.lift₂`. -/
def abstractBehavior (model : Finset (Branch Sub PC))
    (q₁ q₂ : Quotient (pcSetoid isa model)) : Prop :=
  ∃ s₁ s₂ : State,
    Quotient.mk (pcSetoid isa model) s₁ = q₁ ∧
    Quotient.mk (pcSetoid isa model) s₂ = q₂ ∧
    branchBehavior isa (↑model : Set (Branch Sub PC)) s₁ s₂

/-- Cross-system bisimulation: an abstraction map `abs` mediates between
    a concrete and an abstract transition system. -/
structure CrossBisimulation {CState AState : Type*}
    (abs : CState → AState)
    (concrete : CState → CState → Prop)
    (abstract : AState → AState → Prop) : Prop where
  forward : ∀ s s', concrete s s' → abstract (abs s) (abs s')
  backward : ∀ s a', abstract (abs s) a' →
    ∃ s', concrete s s' ∧ abs s' = a'

/-- Forward direction: concrete transition → abstract transition. -/
theorem quotient_forward (model : Finset (Branch Sub PC))
    (behavior : State → State → Prop)
    (h_complete : BranchModel.Complete isa (↑model : Set (Branch Sub PC)) behavior)
    (s s' : State) (h : behavior s s') :
    abstractBehavior isa model
      (Quotient.mk (pcSetoid isa model) s)
      (Quotient.mk (pcSetoid isa model) s') := by
  obtain ⟨b, hb, hsat, heval⟩ := h_complete s s' h
  exact ⟨s, s', rfl, rfl, ⟨b, hb, hsat, heval⟩⟩

/-- Backward direction: abstract transition from `[s]` to `a'` implies
    a concrete transition from `s` to some `s'` with `[s'] = a'`.

    Given `abstractBehavior [s] a'`, we get witnesses `s₁, s₂` with
    `[s₁] = [s]` (so `s ≈ s₁`), `[s₂] = a'`, and a branch `b` connecting them.
    By congruence, `b` fires from `s` too (since `s ≈ s₁`).
    By soundness, `behavior s (eval_sub b.sub s)`.
    By congruence, `eval_sub b.sub s ≈ eval_sub b.sub s₁ = s₂`, so `[eval s] = a'`. -/
theorem quotient_backward (model : Finset (Branch Sub PC))
    (behavior : State → State → Prop)
    (h_sound : BranchModel.Sound isa (↑model : Set (Branch Sub PC)) behavior)
    (s : State) (a' : Quotient (pcSetoid isa model))
    (h : abstractBehavior isa model (Quotient.mk (pcSetoid isa model) s) a') :
    ∃ s', behavior s s' ∧ Quotient.mk (pcSetoid isa model) s' = a' := by
  obtain ⟨s₁, s₂, h_eq1, h_eq2, b, hb, hsat1, heval⟩ := h
  -- s ≈ s₁ (from [s] = [s₁])
  have h_equiv : (pcSetoid isa model).r s s₁ :=
    Quotient.exact h_eq1.symm
  -- b fires from s (by congruence)
  have h_fires_s : isa.satisfies s b.pc :=
    pcEquiv_branch_fires isa (Finset.mem_coe.mp hb) (pcEquiv_symm isa h_equiv)
      (hsat1)
  -- behavior s (eval_sub b.sub s) by soundness
  have h_beh : behavior s (isa.eval_sub b.sub s) :=
    h_sound b hb s h_fires_s
  -- eval_sub b.sub s ≈ eval_sub b.sub s₁ (by congruence)
  have h_succ_equiv : (pcSetoid isa model).r
      (isa.eval_sub b.sub s) (isa.eval_sub b.sub s₁) :=
    pcEquiv_eval_sub isa (Finset.mem_coe.mp hb) h_equiv
  -- eval_sub b.sub s₁ = s₂, so eval_sub b.sub s ≈ s₂
  -- Therefore [eval_sub b.sub s] = [s₂] = a'
  refine ⟨isa.eval_sub b.sub s, h_beh, ?_⟩
  rw [← h_eq2]
  apply Quotient.sound
  show (pcSetoid isa model).r (isa.eval_sub b.sub s) s₂
  rw [← heval]
  exact h_succ_equiv

/-- The quotient map is a cross-system bisimulation. -/
theorem quotient_bisimulation (model : Finset (Branch Sub PC))
    (behavior : State → State → Prop)
    (h_sound : BranchModel.Sound isa (↑model : Set (Branch Sub PC)) behavior)
    (h_complete : BranchModel.Complete isa (↑model : Set (Branch Sub PC)) behavior) :
    CrossBisimulation
      (Quotient.mk (pcSetoid isa model))
      behavior
      (abstractBehavior isa model) where
  forward := quotient_forward isa model behavior h_complete
  backward := quotient_backward isa model behavior h_sound

end AbstractSystem


/-! ## Step 4d: Finiteness Bound

The number of abstract states is bounded by `2^|pcClosure model|`.
Each equivalence class is characterized by its "PC signature" — the
subset of closure PCs it satisfies. Distinct classes have distinct
signatures, and signatures are subsets of the closure. -/

section PCSignature

variable {Sub PC State : Type*} [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)
  [h_dec : ∀ (s : State) (φ : PC), Decidable (isa.satisfies s φ)]

/-- The PC signature of a state relative to an explicit closure. -/
noncomputable def pcSignatureWith (closure : Finset PC) (s : State) : Finset PC :=
  closure.filter (fun φ => isa.satisfies s φ)

/-- Equivalent states over an explicit closure have the same signature. -/
theorem pcSignature_eq_of_equivWith
    {closure : Finset PC} {s₁ s₂ : State}
    (h : (pcSetoidWith isa closure).r s₁ s₂) :
    pcSignatureWith isa closure s₁ = pcSignatureWith isa closure s₂ := by
  change pcEquiv isa closure s₁ s₂ at h
  unfold pcSignatureWith
  ext φ
  constructor
  · intro hφ
    rw [Finset.mem_filter] at hφ ⊢
    exact ⟨hφ.1, (h φ hφ.1).mp hφ.2⟩
  · intro hφ
    rw [Finset.mem_filter] at hφ ⊢
    exact ⟨hφ.1, (h φ hφ.1).mpr hφ.2⟩

/-- States with the same explicit-closure signature are equivalent over that closure. -/
theorem equiv_of_pcSignature_eqWith
    {closure : Finset PC} {s₁ s₂ : State}
    (h : pcSignatureWith isa closure s₁ = pcSignatureWith isa closure s₂) :
    (pcSetoidWith isa closure).r s₁ s₂ := by
  change pcEquiv isa closure s₁ s₂
  intro φ hφ
  constructor
  · intro hsat
    have h1 : φ ∈ pcSignatureWith isa closure s₁ :=
      Finset.mem_filter.mpr ⟨hφ, hsat⟩
    rw [h] at h1
    exact (Finset.mem_filter.mp h1).2
  · intro hsat
    have h1 : φ ∈ pcSignatureWith isa closure s₂ :=
      Finset.mem_filter.mpr ⟨hφ, hsat⟩
    rw [← h] at h1
    exact (Finset.mem_filter.mp h1).2

end PCSignature

section Finiteness

variable {Sub PC State : Type*} [DecidableEq PC] [Fintype PC]
  (isa : SymbolicISA Sub PC State)
  [h_dec : ∀ (s : State) (φ : PC), Decidable (isa.satisfies s φ)]

/-- The PC signature of a state: which closure PCs it satisfies. -/
noncomputable def pcSignature (model : Finset (Branch Sub PC)) (s : State) : Finset PC :=
  pcSignatureWith isa (pcClosure isa model) s

/-- Equivalent states have the same signature. -/
theorem pcSignature_eq_of_equiv
    {model : Finset (Branch Sub PC)} {s₁ s₂ : State}
    (h : (pcSetoid isa model).r s₁ s₂) :
    pcSignature isa model s₁ = pcSignature isa model s₂ :=
  pcSignature_eq_of_equivWith isa h

/-- States with the same signature are equivalent. -/
theorem equiv_of_pcSignature_eq
    {model : Finset (Branch Sub PC)} {s₁ s₂ : State}
    (h : pcSignature isa model s₁ = pcSignature isa model s₂) :
    (pcSetoid isa model).r s₁ s₂ :=
  equiv_of_pcSignature_eqWith isa h

/-- Signature characterizes equivalence classes: equal iff equivalent. -/
theorem pcSignature_eq_iff_equiv
    {model : Finset (Branch Sub PC)} {s₁ s₂ : State} :
    pcSignature isa model s₁ = pcSignature isa model s₂ ↔
    (pcSetoid isa model).r s₁ s₂ :=
  ⟨equiv_of_pcSignature_eq isa, pcSignature_eq_of_equiv isa⟩

/-- Lift signature to the quotient (well-defined by `pcSignature_eq_of_equiv`). -/
noncomputable def quotientSignature (model : Finset (Branch Sub PC)) :
    Quotient (pcSetoid isa model) → Finset PC :=
  Quotient.lift (pcSignature isa model) (fun _ _ h => pcSignature_eq_of_equiv isa h)

/-- The quotient signature is injective: distinct classes have distinct signatures. -/
theorem quotientSignature_injective (model : Finset (Branch Sub PC)) :
    Function.Injective (quotientSignature isa model) := by
  intro q₁ q₂ h
  obtain ⟨s₁, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨s₂, rfl⟩ := Quotient.exists_rep q₂
  apply Quotient.sound
  exact equiv_of_pcSignature_eq isa h

/-- Injection into the powerset of the closure (for the tight finiteness bound). -/
noncomputable def quotientSignaturePow (model : Finset (Branch Sub PC)) :
    Quotient (pcSetoid isa model) → ↥(pcClosure isa model).powerset :=
  fun q => ⟨quotientSignature isa model q, Finset.mem_powerset.mpr (by
    obtain ⟨s, rfl⟩ := Quotient.exists_rep q
    exact Finset.filter_subset _ _)⟩

theorem quotientSignaturePow_injective (model : Finset (Branch Sub PC)) :
    Function.Injective (quotientSignaturePow isa model) := by
  intro q₁ q₂ h
  exact quotientSignature_injective isa model (congr_arg Subtype.val h)

/-- The quotient has finitely many states (via injection into the closure's powerset). -/
noncomputable instance abstractStateFintype (model : Finset (Branch Sub PC)) :
    Fintype (Quotient (pcSetoid isa model)) :=
  Fintype.ofInjective (quotientSignaturePow isa model)
    (quotientSignaturePow_injective isa model)

/-- The number of abstract states is at most `2^|pcClosure model|`. -/
theorem abstractState_card_bound (model : Finset (Branch Sub PC)) :
    Fintype.card (Quotient (pcSetoid isa model)) ≤ 2 ^ (pcClosure isa model).card := by
  calc Fintype.card (Quotient (pcSetoid isa model))
      ≤ Fintype.card ↥(pcClosure isa model).powerset :=
        Fintype.card_le_of_injective (quotientSignaturePow isa model)
          (quotientSignaturePow_injective isa model)
    _ = (pcClosure isa model).powerset.card := Fintype.card_coe _
    _ = 2 ^ (pcClosure isa model).card := Finset.card_powerset _

end Finiteness


/-! ## Step 4d': Finiteness for Explicit Closures

The same finiteness bound applies to quotients over explicit closures,
without requiring `[Fintype PC]`. This generalizes Step 4d to the
explicit-closure setting needed for STS1 when `PC` is infinite. -/

section FinitenessWith

variable {Sub PC State : Type*} [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)
  [h_dec : ∀ (s : State) (φ : PC), Decidable (isa.satisfies s φ)]

/-- Lift signature to the quotient over an explicit closure. -/
noncomputable def quotientSignatureWith (closure : Finset PC) :
    Quotient (pcSetoidWith isa closure) → Finset PC :=
  Quotient.lift (pcSignatureWith isa closure)
    (fun _ _ h => pcSignature_eq_of_equivWith isa h)

/-- The quotient signature over an explicit closure is injective. -/
theorem quotientSignatureWith_injective (closure : Finset PC) :
    Function.Injective (quotientSignatureWith isa closure) := by
  intro q₁ q₂ h
  obtain ⟨s₁, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨s₂, rfl⟩ := Quotient.exists_rep q₂
  apply Quotient.sound
  exact equiv_of_pcSignature_eqWith isa h

/-- Injection into the powerset of the explicit closure. -/
noncomputable def quotientSignaturePowWith (closure : Finset PC) :
    Quotient (pcSetoidWith isa closure) → ↥closure.powerset :=
  fun q => ⟨quotientSignatureWith isa closure q, Finset.mem_powerset.mpr (by
    obtain ⟨s, rfl⟩ := Quotient.exists_rep q
    exact Finset.filter_subset _ _)⟩

theorem quotientSignaturePowWith_injective (closure : Finset PC) :
    Function.Injective (quotientSignaturePowWith isa closure) := by
  intro q₁ q₂ h
  exact quotientSignatureWith_injective isa closure (congr_arg Subtype.val h)

/-- The quotient over an explicit closure has finitely many states. -/
noncomputable instance abstractStateWithFintype (closure : Finset PC) :
    Fintype (Quotient (pcSetoidWith isa closure)) :=
  Fintype.ofInjective (quotientSignaturePowWith isa closure)
    (quotientSignaturePowWith_injective isa closure)

/-- The number of abstract states over an explicit closure is at most 2^|closure|. -/
theorem abstractStateWith_card_bound (closure : Finset PC) :
    Fintype.card (Quotient (pcSetoidWith isa closure)) ≤ 2 ^ closure.card := by
  calc Fintype.card (Quotient (pcSetoidWith isa closure))
      ≤ Fintype.card ↥closure.powerset :=
        Fintype.card_le_of_injective (quotientSignaturePowWith isa closure)
          (quotientSignaturePowWith_injective isa closure)
    _ = closure.powerset.card := Fintype.card_coe _
    _ = 2 ^ closure.card := Finset.card_powerset _

end FinitenessWith


/-! ## Step 4c': Abstract System with Explicit Closures

The abstract transition system and cross-system bisimulation generalized
to work with an explicit finite closure, without requiring `[Fintype PC]`.

A sound and complete branch model induces a finite abstract transition
system that is cross-bisimilar to the concrete system. The abstract state
space has at most 2^|closure| states (by `abstractStateWith_card_bound`,
which additionally requires decidable `satisfies`).

This gives an STS1-style result (cf. HMR05 Theorem 1A): a finite
cross-bisimilar quotient. Note: this is not a proof that the quotient
relation is the coarsest bisimulation — it proves the existence of
a sufficiently fine finite bisimulation.

The closure hypotheses (`h_contains`, `h_closed`) replace the global
`[Fintype PC]` requirement. They say: model PCs lie in the closure, and
the closure is closed under lifting through model substitutions. -/

section AbstractSystemWith

variable {Sub PC State : Type*} [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Abstract transition over an explicit closure. -/
def abstractBehaviorWith (model : Finset (Branch Sub PC)) (closure : Finset PC)
    (q₁ q₂ : Quotient (pcSetoidWith isa closure)) : Prop :=
  ∃ s₁ s₂ : State,
    Quotient.mk (pcSetoidWith isa closure) s₁ = q₁ ∧
    Quotient.mk (pcSetoidWith isa closure) s₂ = q₂ ∧
    branchBehavior isa (↑model : Set (Branch Sub PC)) s₁ s₂

/-- Forward direction over explicit closure: concrete → abstract. -/
theorem quotient_forwardWith (model : Finset (Branch Sub PC)) (closure : Finset PC)
    (behavior : State → State → Prop)
    (h_complete : BranchModel.Complete isa (↑model : Set (Branch Sub PC)) behavior)
    (s s' : State) (h : behavior s s') :
    abstractBehaviorWith isa model closure
      (Quotient.mk (pcSetoidWith isa closure) s)
      (Quotient.mk (pcSetoidWith isa closure) s') := by
  obtain ⟨b, hb, hsat, heval⟩ := h_complete s s' h
  exact ⟨s, s', rfl, rfl, ⟨b, hb, hsat, heval⟩⟩

/-- Backward direction over explicit closure: abstract from [s] → concrete from s.

    Given `abstractBehaviorWith [s] a'`, we get witnesses `s₁, s₂` with
    `[s₁] = [s]` (so `s ≈ s₁`), `[s₂] = a'`, and a branch `b` connecting them.
    By `pcEquiv_branch_firesWith`, `b` fires from `s` too.
    By soundness, `behavior s (eval_sub b.sub s)`.
    By `pcEquiv_eval_subWith`, `eval_sub b.sub s ≈ eval_sub b.sub s₁ = s₂`,
    so `[eval s] = a'`. -/
theorem quotient_backwardWith (model : Finset (Branch Sub PC)) (closure : Finset PC)
    (h_contains : ∀ b ∈ model, b.pc ∈ closure)
    (h_closed : ∀ b ∈ model, ∀ φ ∈ closure, isa.pc_lift b.sub φ ∈ closure)
    (behavior : State → State → Prop)
    (h_sound : BranchModel.Sound isa (↑model : Set (Branch Sub PC)) behavior)
    (s : State) (a' : Quotient (pcSetoidWith isa closure))
    (h : abstractBehaviorWith isa model closure
      (Quotient.mk (pcSetoidWith isa closure) s) a') :
    ∃ s', behavior s s' ∧ Quotient.mk (pcSetoidWith isa closure) s' = a' := by
  obtain ⟨s₁, s₂, h_eq1, h_eq2, b, hb, hsat1, heval⟩ := h
  have h_equiv : (pcSetoidWith isa closure).r s s₁ :=
    Quotient.exact h_eq1.symm
  have h_fires_s : isa.satisfies s b.pc :=
    pcEquiv_branch_firesWith isa (h_contains b (Finset.mem_coe.mp hb))
      (pcEquiv_symm isa h_equiv) hsat1
  have h_beh : behavior s (isa.eval_sub b.sub s) :=
    h_sound b hb s h_fires_s
  have h_succ_equiv : (pcSetoidWith isa closure).r
      (isa.eval_sub b.sub s) (isa.eval_sub b.sub s₁) :=
    pcEquiv_eval_subWith isa
      (fun φ hφ => h_closed b (Finset.mem_coe.mp hb) φ hφ) h_equiv
  refine ⟨isa.eval_sub b.sub s, h_beh, ?_⟩
  rw [← h_eq2]
  apply Quotient.sound
  show (pcSetoidWith isa closure).r (isa.eval_sub b.sub s) s₂
  rw [← heval]
  exact h_succ_equiv

/-- The quotient map is a cross-system bisimulation over an explicit closure.

    Combined with `abstractStateWith_card_bound` (which additionally requires
    decidable `satisfies`), this gives the STS1-style result: a finite abstract
    transition system, cross-bisimilar to the concrete system, with at most
    2^|closure| states. Note: this proves the existence of a finite cross-bisimilar
    quotient, not that it is the coarsest bisimulation quotient. -/
theorem quotient_bisimulationWith (model : Finset (Branch Sub PC)) (closure : Finset PC)
    (h_contains : ∀ b ∈ model, b.pc ∈ closure)
    (h_closed : ∀ b ∈ model, ∀ φ ∈ closure, isa.pc_lift b.sub φ ∈ closure)
    (behavior : State → State → Prop)
    (h_sound : BranchModel.Sound isa (↑model : Set (Branch Sub PC)) behavior)
    (h_complete : BranchModel.Complete isa (↑model : Set (Branch Sub PC)) behavior) :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith isa closure))
      behavior
      (abstractBehaviorWith isa model closure) where
  forward := quotient_forwardWith isa model closure behavior h_complete
  backward := quotient_backwardWith isa model closure h_contains h_closed behavior h_sound

end AbstractSystemWith


/-! ## Step 4e: End-to-End Theorem

Combining Phase 2 convergence with Phase 4 quotient bisimulation:
a productive, target-bounded oracle with a complete target converges to
a model whose quotient is a finite abstract system bisimilar to the
concrete system. -/

section EndToEnd

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC] [Fintype PC]

/-- End-to-end: oracle convergence yields a finite quotient bisimulation.

    Given a productive, target-bounded oracle with a complete target:
    1. The oracle converges to a sound and complete model (Phase 2)
    2. The quotient by PC-equivalence is cross-bisimilar (Phase 4)
    3. The abstract state space has at most `2^|pcClosure|` states

    This IS the publishable result: "we extracted a finite abstract model." -/
theorem quotientBisimulation
    (oracle : BranchOracle Sub PC State)
    [h_dec : ∀ (s : State) (φ : PC), Decidable (oracle.isa.satisfies s φ)]
    (target : Finset (Branch Sub PC))
    (h_productive : oracle.Productive target)
    (h_bounded : oracle.TargetBounded target)
    (h_target_complete : BranchModel.Complete oracle.isa
      (↑target : Set (Branch Sub PC)) oracle.behavior) :
    ∃ n, n ≤ target.card ∧
      CrossBisimulation
        (Quotient.mk (pcSetoid oracle.isa (oracleSequence oracle n)))
        oracle.behavior
        (abstractBehavior oracle.isa (oracleSequence oracle n)) ∧
      Fintype.card (Quotient (pcSetoid oracle.isa (oracleSequence oracle n))) ≤
        2 ^ (pcClosure oracle.isa (oracleSequence oracle n)).card := by
  obtain ⟨n, h_le, h_sound, h_complete⟩ :=
    branchAccumulation_sound_and_complete oracle target h_productive h_bounded h_target_complete
  exact ⟨n, h_le,
    quotient_bisimulation oracle.isa (oracleSequence oracle n) oracle.behavior h_sound h_complete,
    abstractState_card_bound oracle.isa (oracleSequence oracle n)⟩

end EndToEnd
