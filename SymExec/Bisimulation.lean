import SymExec.BranchConvergence

/-!
# Bisimulation from Branch Models

Connects branch model soundness/completeness to the standard verification
concept of bisimulation.

## Architecture

Both the real system and the branch model operate over the same `State` type.
The branch model doesn't introduce an abstract state space — that's composition
(Phase 4), where the quotient by PC-equivalence gives abstract states and labels
emerge from branch clustering.

Bisimulation here is: the identity relation on states is a bisimulation between
the real system and the branch-model-induced system. This means Sound ∧ Complete
is literally equivalent to bisimulation — they're the same statement in different
vocabulary. The value is:

1. Connecting to standard verification language (any reader who knows bisimulation
   immediately understands what Sound ∧ Complete gives).
2. Making the asymmetry during refinement explicit: partial models forward-simulate
   the real system (underapproximation).
3. Providing the foundation for quotient bisimulation in Phase 4.

## Relation to ICTAC

ICTAC Theorem 2 proves `SE_correct` and `SE_complete` for a specific syntax.
Our `Sound` and `Complete` are the parametric versions. This file shows that
parametric Sound ∧ Complete = bisimulation, which is implicit in ICTAC but
never stated as such.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! ## Branch-Induced Behavior

The transition relation a branch model induces on the concrete state space:
`s → s'` iff there exists a branch in the model whose PC `s` satisfies and
whose substitution maps `s` to `s'`. -/

section BranchBehavior

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- The transition relation induced by a branch model on concrete states.
    `branchBehavior isa model s s'` holds iff some branch in `model` has
    its PC satisfied by `s` and its substitution maps `s` to `s'`. -/
def branchBehavior (model : BranchModel Sub PC) (s s' : State) : Prop :=
  ∃ b ∈ model, isa.satisfies s b.pc ∧ isa.eval_sub b.sub s = s'

end BranchBehavior


/-! ## Sound/Complete as Containment

Soundness and completeness are exactly the two containment directions
between `branchBehavior` and the real behavior. -/

section Containment

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- Soundness ↔ branch-induced behavior is contained in real behavior. -/
theorem sound_iff_branch_sub_behavior
    (model : BranchModel Sub PC) (behavior : State → State → Prop) :
    model.Sound isa behavior ↔
    (∀ s s', branchBehavior isa model s s' → behavior s s') := by
  constructor
  · intro h_sound s s' ⟨b, hb, hsat, heval⟩
    rw [← heval]
    exact h_sound b hb s hsat
  · intro h_sub b hb s hsat
    exact h_sub s _ ⟨b, hb, hsat, rfl⟩

/-- Completeness ↔ real behavior is contained in branch-induced behavior. -/
theorem complete_iff_behavior_sub_branch
    (model : BranchModel Sub PC) (behavior : State → State → Prop) :
    model.Complete isa behavior ↔
    (∀ s s', behavior s s' → branchBehavior isa model s s') := by
  constructor
  · intro h_complete s s' hbeh
    obtain ⟨b, hb, hsat, heval⟩ := h_complete s s' hbeh
    exact ⟨b, hb, hsat, heval⟩
  · intro h_sub s s' hbeh
    obtain ⟨b, hb, hsat, heval⟩ := h_sub s s' hbeh
    exact ⟨b, hb, hsat, heval⟩

/-- Sound ∧ Complete ↔ branch-induced behavior equals real behavior. -/
theorem sound_complete_iff_eq
    (model : BranchModel Sub PC) (behavior : State → State → Prop) :
    model.Sound isa behavior ∧ model.Complete isa behavior ↔
    (∀ s s', branchBehavior isa model s s' ↔ behavior s s') := by
  constructor
  · intro ⟨h_sound, h_complete⟩ s s'
    exact ⟨(sound_iff_branch_sub_behavior isa model behavior).mp h_sound s s',
           (complete_iff_behavior_sub_branch isa model behavior).mp h_complete s s'⟩
  · intro h_eq
    exact ⟨(sound_iff_branch_sub_behavior isa model behavior).mpr (fun s s' h => (h_eq s s').mp h),
           (complete_iff_behavior_sub_branch isa model behavior).mpr (fun s s' h => (h_eq s s').mpr h)⟩

end Containment


/-! ## Simulation and Bisimulation

For same-state-space systems, simulation is just relation containment
and bisimulation is relation equality. These are standard definitions
specialized to the identity relation on states. -/

section SimBisim

variable {State : Type*}

/-- `sys₁` simulates `sys₂`: every transition of `sys₁` is a transition of `sys₂`.
    For same-state-space systems, this is containment of transition relations. -/
def Simulates (sys₁ sys₂ : State → State → Prop) : Prop :=
  ∀ s s', sys₁ s s' → sys₂ s s'

/-- Two systems are bisimilar: each simulates the other.
    For same-state-space systems, this is equality of transition relations. -/
def Bisimilar (sys₁ sys₂ : State → State → Prop) : Prop :=
  Simulates sys₁ sys₂ ∧ Simulates sys₂ sys₁

theorem Bisimilar.symm {sys₁ sys₂ : State → State → Prop}
    (h : Bisimilar sys₁ sys₂) : Bisimilar sys₂ sys₁ :=
  ⟨h.2, h.1⟩

theorem Bisimilar.refl (sys : State → State → Prop) :
    Bisimilar sys sys :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem Bisimilar.trans {sys₁ sys₂ sys₃ : State → State → Prop}
    (h₁₂ : Bisimilar sys₁ sys₂) (h₂₃ : Bisimilar sys₂ sys₃) :
    Bisimilar sys₁ sys₃ :=
  ⟨fun s s' h => h₂₃.1 s s' (h₁₂.1 s s' h),
   fun s s' h => h₁₂.2 s s' (h₂₃.2 s s' h)⟩

end SimBisim


/-! ## Connecting Branches to Simulation/Bisimulation

Sound → branch model simulates real system (underapproximation).
Complete → real system simulates branch model.
Sound ∧ Complete → bisimilar. -/

section BranchSimBisim

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- Soundness implies the branch model forward-simulates the real system:
    every branch-induced transition is a real transition. -/
theorem sound_implies_simulation
    {model : BranchModel Sub PC} {behavior : State → State → Prop}
    (h_sound : model.Sound isa behavior) :
    Simulates (branchBehavior isa model) behavior :=
  (sound_iff_branch_sub_behavior isa model behavior).mp h_sound

/-- Completeness implies the real system forward-simulates the branch model:
    every real transition is a branch-induced transition. -/
theorem complete_implies_simulation
    {model : BranchModel Sub PC} {behavior : State → State → Prop}
    (h_complete : model.Complete isa behavior) :
    Simulates behavior (branchBehavior isa model) :=
  (complete_iff_behavior_sub_branch isa model behavior).mp h_complete

/-- Sound ∧ Complete → bisimilar. -/
theorem sound_complete_implies_bisimilar
    {model : BranchModel Sub PC} {behavior : State → State → Prop}
    (h_sound : model.Sound isa behavior)
    (h_complete : model.Complete isa behavior) :
    Bisimilar (branchBehavior isa model) behavior :=
  ⟨sound_implies_simulation isa h_sound,
   complete_implies_simulation isa h_complete⟩

/-- Bisimilar ↔ Sound ∧ Complete: exact equivalence. -/
theorem sound_complete_iff_bisimilar
    (model : BranchModel Sub PC) (behavior : State → State → Prop) :
    model.Sound isa behavior ∧ model.Complete isa behavior ↔
    Bisimilar (branchBehavior isa model) behavior := by
  constructor
  · intro ⟨hs, hc⟩
    exact sound_complete_implies_bisimilar isa hs hc
  · intro ⟨h_fwd, h_bwd⟩
    exact ⟨(sound_iff_branch_sub_behavior isa model behavior).mpr h_fwd,
           (complete_iff_behavior_sub_branch isa model behavior).mpr h_bwd⟩

end BranchSimBisim


/-! ## End-to-End: Oracle Convergence → Bisimulation

Connecting Phase 2's convergence result to bisimulation:
- At convergence, the oracle sequence produces a bisimilar model.
- At EVERY step (not just convergence), partial models forward-simulate
  the real system — they are sound underapproximations. -/

section EndToEnd

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]

/-- At every step of oracle accumulation, the partial model forward-simulates
    the real system. Partial models are underapproximations: they can only
    produce transitions that actually exist, but may miss some. -/
theorem oracleSequence_simulates (oracle : BranchOracle Sub PC State) (n : ℕ) :
    Simulates
      (branchBehavior oracle.isa (↑(oracleSequence oracle n) : Set (Branch Sub PC)))
      oracle.behavior :=
  sound_implies_simulation oracle.isa (oracleSequence_sound oracle n)

/-- End-to-end: a productive, target-bounded oracle with a complete target
    converges to a bisimilar model in at most |target| steps.

    This is the bisimulation formulation of `branchAccumulation_sound_and_complete`:
    same hypotheses, same bound, but the conclusion is stated in standard
    verification vocabulary. -/
theorem branchAccumulation_bisimilar
    (oracle : BranchOracle Sub PC State)
    (target : Finset (Branch Sub PC))
    (h_productive : oracle.Productive target)
    (h_bounded : oracle.TargetBounded target)
    (h_target_complete : BranchModel.Complete oracle.isa
      (↑target : Set (Branch Sub PC)) oracle.behavior) :
    ∃ n, n ≤ target.card ∧
      Bisimilar
        (branchBehavior oracle.isa (↑(oracleSequence oracle n) : Set (Branch Sub PC)))
        oracle.behavior := by
  obtain ⟨n, h_le, h_sound, h_complete⟩ :=
    branchAccumulation_sound_and_complete oracle target h_productive h_bounded h_target_complete
  exact ⟨n, h_le, sound_complete_implies_bisimilar oracle.isa h_sound h_complete⟩

end EndToEnd
