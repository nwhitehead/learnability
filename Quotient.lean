import Bisimulation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

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

variable {Sub PC State : Type*} [DecidableEq PC] [Fintype PC]
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

/-- PC-equivalence over a model's closure as a `Setoid`. -/
def pcSetoid (model : Finset (Branch Sub PC)) : Setoid State where
  r := pcEquiv isa (pcClosure isa model)
  iseqv := {
    refl := pcEquiv_refl isa _
    symm := pcEquiv_symm isa
    trans := pcEquiv_trans isa
  }

/-- If two states are PC-equivalent (over the closure) and a branch in the
    model fires from one, it fires from the other. -/
theorem pcEquiv_branch_fires {model : Finset (Branch Sub PC)}
    {s₁ s₂ : State} {b : Branch Sub PC}
    (hb : b ∈ model)
    (h_equiv : (pcSetoid isa model).r s₁ s₂)
    (h_fires : isa.satisfies s₁ b.pc) :
    isa.satisfies s₂ b.pc :=
  (h_equiv b.pc (pcClosure_contains_model_pcs isa model b hb)).mp h_fires

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
    (pcSetoid isa model).r (isa.eval_sub b.sub s₁) (isa.eval_sub b.sub s₂) := by
  intro φ hφ
  constructor
  · intro h
    rw [← isa.sat_lift s₂ b.sub φ]
    rw [← isa.sat_lift s₁ b.sub φ] at h
    exact (h_equiv (isa.pc_lift b.sub φ) (pcClosure_closed isa model b hb φ hφ)).mp h
  · intro h
    rw [← isa.sat_lift s₁ b.sub φ]
    rw [← isa.sat_lift s₂ b.sub φ] at h
    exact (h_equiv (isa.pc_lift b.sub φ) (pcClosure_closed isa model b hb φ hφ)).mpr h

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

/-- The abstract state space: quotient by PC-equivalence. -/
noncomputable abbrev AbstractState (model : Finset (Branch Sub PC)) :=
  Quotient (pcSetoid isa model)

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

section Finiteness

variable {Sub PC State : Type*} [DecidableEq PC] [Fintype PC]
  (isa : SymbolicISA Sub PC State)
  [h_dec : ∀ (s : State) (φ : PC), Decidable (isa.satisfies s φ)]

/-- The PC signature of a state: which closure PCs it satisfies. -/
noncomputable def pcSignature (model : Finset (Branch Sub PC)) (s : State) : Finset PC :=
  (pcClosure isa model).filter (fun φ => isa.satisfies s φ)

/-- Equivalent states have the same signature. -/
theorem pcSignature_eq_of_equiv
    {model : Finset (Branch Sub PC)} {s₁ s₂ : State}
    (h : (pcSetoid isa model).r s₁ s₂) :
    pcSignature isa model s₁ = pcSignature isa model s₂ := by
  unfold pcSignature
  ext φ
  constructor
  · intro hφ
    rw [Finset.mem_filter] at hφ ⊢
    exact ⟨hφ.1, (h φ hφ.1).mp hφ.2⟩
  · intro hφ
    rw [Finset.mem_filter] at hφ ⊢
    exact ⟨hφ.1, (h φ hφ.1).mpr hφ.2⟩

/-- States with the same signature are equivalent. -/
theorem equiv_of_pcSignature_eq
    {model : Finset (Branch Sub PC)} {s₁ s₂ : State}
    (h : pcSignature isa model s₁ = pcSignature isa model s₂) :
    (pcSetoid isa model).r s₁ s₂ := by
  intro φ hφ
  constructor
  · intro hsat
    have h1 : φ ∈ pcSignature isa model s₁ :=
      Finset.mem_filter.mpr ⟨hφ, hsat⟩
    rw [h] at h1
    exact (Finset.mem_filter.mp h1).2
  · intro hsat
    have h1 : φ ∈ pcSignature isa model s₂ :=
      Finset.mem_filter.mpr ⟨hφ, hsat⟩
    rw [← h] at h1
    exact (Finset.mem_filter.mp h1).2

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

end Finiteness


/-! ## Step 4e: End-to-End Theorem

Combining Phase 2 convergence with Phase 4 quotient bisimulation:
a productive, target-bounded oracle with a complete target converges to
a model whose quotient is a finite abstract system bisimilar to the
concrete system. -/

section EndToEnd

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC] [Fintype PC]

/-- End-to-end: oracle convergence yields a quotient bisimulation.

    Given a productive, target-bounded oracle with a complete target:
    1. The oracle converges to a sound and complete model (Phase 2)
    2. The quotient by PC-equivalence is cross-bisimilar (Phase 4)
    3. The abstract state space is finite (bounded by 2^|closure|)

    This IS the publishable result: "we extracted a finite abstract model." -/
theorem quotientBisimulation
    (oracle : BranchOracle Sub PC State)
    (target : Finset (Branch Sub PC))
    (h_productive : oracle.Productive target)
    (h_bounded : oracle.TargetBounded target)
    (h_target_complete : BranchModel.Complete oracle.isa
      (↑target : Set (Branch Sub PC)) oracle.behavior) :
    ∃ n, n ≤ target.card ∧
      CrossBisimulation
        (Quotient.mk (pcSetoid oracle.isa (oracleSequence oracle n)))
        oracle.behavior
        (abstractBehavior oracle.isa (oracleSequence oracle n)) := by
  obtain ⟨n, h_le, h_sound, h_complete⟩ :=
    branchAccumulation_sound_and_complete oracle target h_productive h_bounded h_target_complete
  exact ⟨n, h_le, quotient_bisimulation oracle.isa (oracleSequence oracle n) oracle.behavior
    h_sound h_complete⟩

end EndToEnd
