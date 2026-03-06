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
