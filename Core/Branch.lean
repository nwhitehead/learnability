import Core.SymbolicISA
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

/-!
# Branches and Branch Models

A branch is a pair `(sub, pc)` — the symbolic execution output for one path
through a program. ICTAC Definition 11:
`denot__S(p) = {(Sub(t), PC(t)) | t ∈ traces(p)}`.

A branch model is a set of branches describing a system's behavior.
**Label-free**: branches are not indexed by labels at this stage.
Labels emerge later from branch clustering (dispatch structure readable
from PCs — see Composition.lean).

## Soundness and Completeness

These are the parametric versions of ICTAC Theorem 2:

- **Soundness** (from `SE_correct`): every satisfiable branch corresponds
  to a real transition. If you can satisfy the PC, applying the substitution
  gives you a real successor state.

- **Completeness** (from `SE_complete`): every real transition is witnessed
  by some branch. For every reachable transition `s → s'`, there's a branch
  whose PC `s` satisfies and whose substitution maps `s` to `s'`.

Together, Sound ∧ Complete is the branch-level analog of bisimulation:
the model exactly characterizes the system's behavior.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A branch: one path through symbolic execution.
    ICTAC: `Branch = sub * Bexpr` (Programs.v line 296). -/
structure Branch (Sub : Type*) (PC : Type*) where
  /-- The substitution effect of this execution path. -/
  sub : Sub
  /-- The path condition: under what states this path is taken. -/
  pc : PC
  deriving DecidableEq

section BranchOps

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- The trivial branch: identity substitution, always-true PC.
    Corresponds to ICTAC's `TSkip`: `trace_denot__S TSkip = (id_sub, BTrue)`. -/
def Branch.skip : Branch Sub PC :=
  { sub := isa.id_sub
  , pc := isa.pc_true }

/-- Sequential composition of branches.
    ICTAC: `Sub(t₁;t₂) = compose_subs (Sub t₁) (Sub t₂)` and
    `PC(t₁;t₂) = BAnd (PC t₁) (Bapply (Sub t₁) (PC t₂))`.
    (Programs.v, `sub_trace_app` and `pc_trace_app`.) -/
def Branch.compose (b₁ b₂ : Branch Sub PC) : Branch Sub PC :=
  { sub := isa.compose_sub b₁.sub b₂.sub
  , pc := isa.pc_and b₁.pc (isa.pc_lift b₁.sub b₂.pc) }

/-- A state satisfies a branch iff it satisfies the branch's path condition. -/
def Branch.satisfiedBy (b : Branch Sub PC) (s : State) : Prop :=
  isa.satisfies s b.pc

/-- The effect of a branch on a state: apply the substitution. -/
def Branch.effect (b : Branch Sub PC) (s : State) : State :=
  isa.eval_sub b.sub s

/-- Every state satisfies the trivial branch. -/
theorem Branch.skip_satisfiedBy (s : State) :
    (Branch.skip isa).satisfiedBy isa s :=
  isa.sat_true s

/-- The trivial branch has no effect. -/
theorem Branch.skip_effect (s : State) :
    (Branch.skip isa).effect isa s = s :=
  isa.eval_id s

/-- Satisfaction of a composed branch decomposes into satisfaction of parts.
    This is the semantic content of ICTAC's `pc_trace_app`:
    `s |= PC(t₁;t₂)` iff `s |= PC(t₁)` and `eval(Sub(t₁), s) |= PC(t₂)`. -/
theorem Branch.compose_satisfiedBy (b₁ b₂ : Branch Sub PC) (s : State) :
    (b₁.compose isa b₂).satisfiedBy isa s ↔
    b₁.satisfiedBy isa s ∧ b₂.satisfiedBy isa (b₁.effect isa s) := by
  unfold satisfiedBy compose effect
  constructor
  · intro h
    have h' := (isa.sat_and s b₁.pc (isa.pc_lift b₁.sub b₂.pc)).mp h
    exact ⟨h'.1, (isa.sat_lift s b₁.sub b₂.pc).mp h'.2⟩
  · intro ⟨h1, h2⟩
    exact (isa.sat_and s b₁.pc (isa.pc_lift b₁.sub b₂.pc)).mpr
      ⟨h1, (isa.sat_lift s b₁.sub b₂.pc).mpr h2⟩

/-- Effect of composed branch = sequential application.
    This is `eval_compose` lifted to branches. -/
theorem Branch.compose_effect (b₁ b₂ : Branch Sub PC) (s : State) :
    (b₁.compose isa b₂).effect isa s = b₂.effect isa (b₁.effect isa s) := by
  unfold effect compose
  exact isa.eval_compose b₁.sub b₂.sub s

end BranchOps


/-! ## Branch Models -/

/-- A branch model: a set of branches describing a system's behavior.
    Label-free — branches are not indexed by labels.

    At the symex level, the oracle produces branches without labels.
    Labels (handlers / dispatch categories) emerge from branch clustering:
    the PCs partition input space into regions, each region corresponding
    to a different dispatch target. This partition IS the label structure,
    readable from the PCs. -/
abbrev BranchModel (Sub : Type*) (PC : Type*) := Set (Branch Sub PC)


/-! ## Soundness and Completeness -/

section BranchModelProperties

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- Soundness: every satisfiable branch corresponds to a real transition.
    Parametric version of ICTAC Theorem 2, `SE_correct`. -/
def BranchModel.Sound (model : BranchModel Sub PC) (behavior : State → State → Prop) : Prop :=
  ∀ b ∈ model, ∀ (s : State),
    isa.satisfies s b.pc → behavior s (isa.eval_sub b.sub s)

/-- Completeness: every real transition is witnessed by some branch.
    Parametric version of ICTAC Theorem 2, `SE_complete`. -/
def BranchModel.Complete (model : BranchModel Sub PC) (behavior : State → State → Prop) : Prop :=
  ∀ (s s' : State), behavior s s' →
    ∃ b ∈ model, isa.satisfies s b.pc ∧ isa.eval_sub b.sub s = s'

/-- Soundness is downward-closed: subsets of sound models are sound. -/
theorem BranchModel.Sound.subset {model₁ model₂ : BranchModel Sub PC}
    {behavior : State → State → Prop}
    (h_sound : model₂.Sound isa behavior)
    (h_sub : model₁ ⊆ model₂) :
    model₁.Sound isa behavior :=
  fun b hb s hsat => h_sound b (h_sub hb) s hsat

/-- Completeness is upward-closed: supersets of complete models are complete. -/
theorem BranchModel.Complete.superset {model₁ model₂ : BranchModel Sub PC}
    {behavior : State → State → Prop}
    (h_complete : model₁.Complete isa behavior)
    (h_sub : model₁ ⊆ model₂) :
    model₂.Complete isa behavior := by
  intro s s' hbeh
  obtain ⟨b, hb, hsat, heval⟩ := h_complete s s' hbeh
  exact ⟨b, h_sub hb, hsat, heval⟩

/-- The empty model is trivially sound. -/
theorem BranchModel.Sound.empty (behavior : State → State → Prop) :
    (∅ : BranchModel Sub PC).Sound isa behavior := by
  intro b hb; simp at hb

/-- Inserting a sound branch into a sound model preserves soundness.
    This is the key lemma for oracle accumulation: the oracle produces
    a branch known to be sound, we add it, soundness is preserved. -/
theorem BranchModel.Sound.insert {model : BranchModel Sub PC}
    {behavior : State → State → Prop}
    (h_sound : model.Sound isa behavior)
    {b : Branch Sub PC}
    (h_b : ∀ (s : State), isa.satisfies s b.pc → behavior s (isa.eval_sub b.sub s)) :
    (insert b model).Sound isa behavior := by
  intro b' hb' s hsat
  simp [Set.mem_insert_iff] at hb'
  rcases hb' with rfl | hb'
  · exact h_b s hsat
  · exact h_sound b' hb' s hsat

end BranchModelProperties
