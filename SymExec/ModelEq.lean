import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union

/-!
# Observation-Level Model Equivalence

This file defines semantic equivalence of symbolic summary families relative to:

- `Relevant : State → Prop`, the states we care about
- `observe : State → Obs`, the projection/extraction observable

The key design point is that equivalence is stated over *denoted observable behavior*,
not syntactic equality of summaries. This is the right level for convergence: dead
or redundant summaries do not matter if they never change relevant observations.

The file is generic over any summary type equipped with:

- `enabled : Summary → State → Prop`
- `apply   : Summary → State → State`

This keeps the theory ISA-agnostic. VEX-specific instantiation comes later.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

section ObservationModel

variable {Summary State Obs : Type*}

/-- A summary family denotes an observation `o` from input state `s` when `s` is relevant
    and some enabled summary in the family produces a successor observed as `o`. -/
def ModelDenotesObs
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    (M : Finset Summary) (s : State) (o : Obs) : Prop :=
  Relevant s ∧ ∃ summary ∈ M, enabled summary s ∧ observe (apply summary s) = o

/-- Two summaries are equivalent when they induce the same observable denotation
    on all relevant states. -/
def SummaryEq
    [DecidableEq Summary]
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    (a b : Summary) : Prop :=
  ∀ s o,
    ModelDenotesObs enabled apply Relevant observe ({a} : Finset Summary) s o ↔
      ModelDenotesObs enabled apply Relevant observe ({b} : Finset Summary) s o

/-- Two summary families are equivalent when they induce the same observable denotation
    on all relevant states. -/
def ModelEq
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    (M N : Finset Summary) : Prop :=
  ∀ s o,
    ModelDenotesObs enabled apply Relevant observe M s o ↔
      ModelDenotesObs enabled apply Relevant observe N s o

/-- Strongest observation-level equivalence: compare concrete successor states directly. -/
abbrev ModelEqState
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (M N : Finset Summary) : Prop :=
  ModelEq enabled apply Relevant (fun s => s) M N

theorem ModelDenotesObs.mono
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    {M N : Finset Summary} (h_sub : M ⊆ N) :
    ∀ {s o},
      ModelDenotesObs enabled apply Relevant observe M s o →
      ModelDenotesObs enabled apply Relevant observe N s o := by
  intro s o h
  rcases h with ⟨hRel, summary, hMem, hEnabled, hObs⟩
  exact ⟨hRel, summary, h_sub hMem, hEnabled, hObs⟩

theorem SummaryEq.refl
    [DecidableEq Summary]
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    (a : Summary) :
    SummaryEq enabled apply Relevant observe a a := by
  intro s o
  rfl

theorem SummaryEq.symm
    [DecidableEq Summary]
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    {a b : Summary}
    (h : SummaryEq enabled apply Relevant observe a b) :
    SummaryEq enabled apply Relevant observe b a := by
  intro s o
  exact (h s o).symm

theorem SummaryEq.trans
    [DecidableEq Summary]
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    {a b c : Summary}
    (h₁ : SummaryEq enabled apply Relevant observe a b)
    (h₂ : SummaryEq enabled apply Relevant observe b c) :
    SummaryEq enabled apply Relevant observe a c := by
  intro s o
  exact Iff.trans (h₁ s o) (h₂ s o)

theorem ModelEq.refl
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    (M : Finset Summary) :
    ModelEq enabled apply Relevant observe M M := by
  intro s o
  rfl

theorem ModelEq.symm
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    {M N : Finset Summary}
    (h : ModelEq enabled apply Relevant observe M N) :
    ModelEq enabled apply Relevant observe N M := by
  intro s o
  exact (h s o).symm

theorem ModelEq.trans
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    {M N P : Finset Summary}
    (h₁ : ModelEq enabled apply Relevant observe M N)
    (h₂ : ModelEq enabled apply Relevant observe N P) :
    ModelEq enabled apply Relevant observe M P := by
  intro s o
  exact Iff.trans (h₁ s o) (h₂ s o)

/-- Adding a summary that is never enabled on relevant states does not change the model. -/
theorem modelEq_insert_dead
    [DecidableEq Summary]
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    (M : Finset Summary) (b : Summary)
    (hdead : ∀ s, Relevant s → ¬ enabled b s) :
    ModelEq enabled apply Relevant observe (insert b M) M := by
  intro s o
  constructor
  · intro h
    rcases h with ⟨hRel, summary, hMem, hEnabled, hObs⟩
    rw [Finset.mem_insert] at hMem
    rcases hMem with rfl | hMem
    · exact False.elim ((hdead s hRel) hEnabled)
    · exact ⟨hRel, summary, hMem, hEnabled, hObs⟩
  · exact ModelDenotesObs.mono enabled apply Relevant observe (Finset.subset_insert _ _) 

/-- Equality of concrete successor denotation implies equality under any observation. -/
theorem modelEqState_implies_modelEq
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    {M N : Finset Summary}
    (h : ModelEqState enabled apply Relevant M N) :
    ModelEq enabled apply Relevant observe M N := by
  intro s o
  constructor
  · intro hM
    rcases hM with ⟨hRel, summary, hMem, hEnabled, hObs⟩
    have hState :
        ModelDenotesObs enabled apply Relevant (fun s => s) M s (apply summary s) := by
      exact ⟨hRel, summary, hMem, hEnabled, rfl⟩
    rcases (h s (apply summary s)).mp hState with ⟨_, summary', hMem', hEnabled', hEq⟩
    exact ⟨hRel, summary', hMem', hEnabled', by simpa [hEq] using hObs⟩
  · intro hN
    rcases hN with ⟨hRel, summary, hMem, hEnabled, hObs⟩
    have hState :
        ModelDenotesObs enabled apply Relevant (fun s => s) N s (apply summary s) := by
      exact ⟨hRel, summary, hMem, hEnabled, rfl⟩
    rcases (h s (apply summary s)).mpr hState with ⟨_, summary', hMem', hEnabled', hEq⟩
    exact ⟨hRel, summary', hMem', hEnabled', by simpa [hEq] using hObs⟩

/-- Model equivalence is congruent on the left under union with a fixed summary family. -/
theorem ModelEq.union_left
    [DecidableEq Summary]
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    {M N K : Finset Summary}
    (h : ModelEq enabled apply Relevant observe M N) :
    ModelEq enabled apply Relevant observe (K ∪ M) (K ∪ N) := by
  intro s o
  constructor
  · intro hKM
    rcases hKM with ⟨hRel, summary, hMem, hEnabled, hObs⟩
    rw [Finset.mem_union] at hMem
    rcases hMem with hK | hM
    · exact ⟨hRel, summary, Finset.mem_union.mpr (Or.inl hK), hEnabled, hObs⟩
    · rcases (h s o).mp ⟨hRel, summary, hM, hEnabled, hObs⟩ with ⟨hRel', summary', hN, hEnabled', hObs'⟩
      exact ⟨hRel', summary', Finset.mem_union.mpr (Or.inr hN), hEnabled', hObs'⟩
  · intro hKN
    rcases hKN with ⟨hRel, summary, hMem, hEnabled, hObs⟩
    rw [Finset.mem_union] at hMem
    rcases hMem with hK | hN
    · exact ⟨hRel, summary, Finset.mem_union.mpr (Or.inl hK), hEnabled, hObs⟩
    · rcases (h s o).mpr ⟨hRel, summary, hN, hEnabled, hObs⟩ with ⟨hRel', summary', hM, hEnabled', hObs'⟩
      exact ⟨hRel', summary', Finset.mem_union.mpr (Or.inr hM), hEnabled', hObs'⟩

/-- Model equivalence is congruent on the right under union with a fixed summary family. -/
theorem ModelEq.union_right
    [DecidableEq Summary]
    (enabled : Summary → State → Prop) (apply : Summary → State → State)
    (Relevant : State → Prop) (observe : State → Obs)
    {M N K : Finset Summary}
    (h : ModelEq enabled apply Relevant observe M N) :
    ModelEq enabled apply Relevant observe (M ∪ K) (N ∪ K) := by
  simpa [Finset.union_comm] using ModelEq.union_left enabled apply Relevant observe (K := K) h

end ObservationModel
