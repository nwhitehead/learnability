import Instances.ISAs.VexModelEq
import Instances.ISAs.VexSummaryISA
import SymExec.CircularCoinduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

abbrev VexLoopSummary (Reg : Type) [DecidableEq Reg] [Fintype Reg] :=
  LoopSummary (SymSub Reg) (SymPC Reg) (ConcreteState Reg) (vexSummaryISA Reg)

/-- An extensional subsystem region: just the relevant inputs, the observable projection,
    and the observed behavior the subsystem is meant to denote. -/
structure Region (Reg : Type) (Obs : Type) [DecidableEq Reg] [Fintype Reg] where
  Relevant : ConcreteState Reg → Prop
  observe : ConcreteState Reg → Obs
  DenotesObs : ConcreteState Reg → Obs → Prop

/-- A finite family of lifted block paths is a complete witness for a region when the
    path-family concrete denotation agrees exactly with the region's observed behavior. -/
def WitnessComplete
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (R : Region Reg Obs)
    (paths : Finset (List (Block Reg))) : Prop :=
  ∀ s o,
    ExecPathFamilyDenotesObs R.Relevant R.observe paths s o ↔
      R.DenotesObs s o

/-- A complete finite path-family witness yields an adequate extracted symbolic model
    for the region it witnesses. -/
theorem extractedModel_of_witnessComplete
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (R : Region Reg Obs)
    (paths : Finset (List (Block Reg)))
    (hcomplete : WitnessComplete R paths) :
    ∀ s o,
      VexModelDenotesObs R.Relevant R.observe (lowerPathFamilySummaries paths) s o ↔
        R.DenotesObs s o := by
  intro s o
  exact Iff.trans
    (lowerPathFamilySummaries_denotesObs_iff_execPathFamily R.Relevant R.observe paths s o)
    (hcomplete s o)

/-- Any two complete witnesses for the same region induce semantically equivalent
    extracted models. -/
theorem completeWitnesses_modelEq
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (R : Region Reg Obs)
    (paths₁ paths₂ : Finset (List (Block Reg)))
    (h₁ : WitnessComplete R paths₁)
    (h₂ : WitnessComplete R paths₂) :
    VexModelEq R.Relevant R.observe
      (lowerPathFamilySummaries paths₁)
      (lowerPathFamilySummaries paths₂) := by
  intro s o
  exact Iff.trans
    (extractedModel_of_witnessComplete R paths₁ h₁ s o)
    (extractedModel_of_witnessComplete R paths₂ h₂ s o).symm

/-- An extensional loop-region specification. This keeps the concrete lifted program and
    instruction-pointer register in scope, but leaves the observed loop behavior itself
    extensional for now. -/
structure LoopRegionSpec (Reg : Type) (Obs : Type) [DecidableEq Reg] [Fintype Reg] where
  program : Program Reg
  ip_reg : Reg
  Relevant : ConcreteState Reg → Prop
  observe : ConcreteState Reg → Obs
  DenotesObs : ConcreteState Reg → Obs → Prop

/-- Forget a loop-region specification down to the generic extensional region object. -/
def LoopRegion
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs) : Region Reg Obs :=
  { Relevant := spec.Relevant
    observe := spec.observe
    DenotesObs := spec.DenotesObs }

@[simp] theorem loopRegion_relevant
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs) :
    (LoopRegion spec).Relevant = spec.Relevant := rfl

@[simp] theorem loopRegion_observe
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs) :
    (LoopRegion spec).observe = spec.observe := rfl

@[simp] theorem loopRegion_denotesObs
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs) :
    (LoopRegion spec).DenotesObs = spec.DenotesObs := rfl

/-- Repeat a lifted loop-body path `n` times by concatenation. -/
def repeatBlockPath
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (body : List (Block Reg)) : Nat → List (Block Reg)
  | 0 => []
  | n + 1 => body ++ repeatBlockPath body n

/-- Finite path-family witness for at-most-`K` iterations of a loop body path. -/
def boundedLoopWitness
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (body : List (Block Reg)) (K : Nat) : Finset (List (Block Reg)) :=
  (Finset.range (K + 1)).image (repeatBlockPath body)

@[simp] theorem repeatBlockPath_zero
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (body : List (Block Reg)) :
    repeatBlockPath body 0 = [] := rfl

@[simp] theorem repeatBlockPath_succ
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (body : List (Block Reg)) (n : Nat) :
    repeatBlockPath body (n + 1) = body ++ repeatBlockPath body n := rfl

theorem nil_mem_boundedLoopWitness
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (body : List (Block Reg)) (K : Nat) :
    [] ∈ boundedLoopWitness body K := by
  refine Finset.mem_image.mpr ?_
  refine ⟨0, ?_, ?_⟩
  · simp
  · simp [repeatBlockPath_zero]

/-- A bounded loop witness is complete when its at-most-`K` path family covers exactly
    the extensional behavior of the loop region. -/
def LoopWitnessComplete
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (body : List (Block Reg)) (K : Nat) : Prop :=
  WitnessComplete (LoopRegion spec) (boundedLoopWitness body K)

/-- Once a bounded loop witness is known to be complete, the extracted summary family is
    immediately an adequate model of the loop region. -/
theorem extractedLoopModel_of_witnessComplete
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (body : List (Block Reg)) (K : Nat)
    (hcomplete : LoopWitnessComplete spec body K) :
    ∀ s o,
      VexModelDenotesObs spec.Relevant spec.observe
        (lowerPathFamilySummaries (boundedLoopWitness body K)) s o ↔
          spec.DenotesObs s o :=
  extractedModel_of_witnessComplete (LoopRegion spec) (boundedLoopWitness body K) hcomplete

/-- Concrete loop-region constructor that reuses the existing `whileBehavior`
    semantics from `CircularCoinduction.lean`. -/
def whileLoopRegionSpec
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (summary : VexLoopSummary Reg)
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs) :
    LoopRegionSpec Reg Obs where
  program := program
  ip_reg := ip_reg
  Relevant := Relevant
  observe := observe
  DenotesObs := fun s o =>
    Relevant s ∧ ∃ s', whileBehavior (isa := vexSummaryISA Reg) summary s s' ∧ observe s' = o

/-- Soundness half of a bounded loop witness: every path in the witness family denotes
    a behavior already included in the extensional loop region. -/
def LoopWitnessSound
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (body : List (Block Reg)) (K : Nat) : Prop :=
  ∀ s o,
    ExecPathFamilyDenotesObs spec.Relevant spec.observe
      (boundedLoopWitness body K) s o →
        spec.DenotesObs s o

/-- Coverage half of a bounded loop witness: every extensional loop behavior appears in
    the bounded path-family witness. This is the actual unrolling-bound obligation that
    later stabilization/finite-state theorems should discharge. -/
def LoopUnrollBound
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (body : List (Block Reg)) (K : Nat) : Prop :=
  ∀ s o,
    spec.DenotesObs s o →
      ExecPathFamilyDenotesObs spec.Relevant spec.observe
        (boundedLoopWitness body K) s o

/-- Specialized name for the exact coverage obligation induced by the concrete
    while-based loop region. This is the hypothesis future stabilization and
    finite-state theorems should discharge. -/
abbrev WhileLoopUnrollBound
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (summary : VexLoopSummary Reg)
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (body : List (Block Reg)) (K : Nat) : Prop :=
  LoopUnrollBound (whileLoopRegionSpec program ip_reg summary Relevant observe) body K

/-- Bounded while behavior is a special case of full while behavior. -/
theorem boundedWhileBehavior_implies_whileBehavior
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : VexLoopSummary Reg) (K : Nat) {s s' : ConcreteState Reg} :
    boundedWhileBehavior (isa := vexSummaryISA Reg) summary K s s' →
      whileBehavior (isa := vexSummaryISA Reg) summary s s' := by
  intro h
  rcases h with ⟨n, _, hIter, hCont, hExit⟩
  exact ⟨n, hIter, hCont, hExit⟩

/-- Membership in the bounded loop witness is exactly repetition of the body path
    some number of times up to the bound. -/
theorem mem_boundedLoopWitness_iff
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (body : List (Block Reg)) (K : Nat) (path : List (Block Reg)) :
    path ∈ boundedLoopWitness body K ↔
      ∃ n, n ≤ K ∧ repeatBlockPath body n = path := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨n, hn, hEq⟩
    exact ⟨n, Finset.mem_range_succ_iff.mp hn, hEq⟩
  · rintro ⟨n, hn, rfl⟩
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range_succ_iff.mpr hn, rfl⟩

/-- A bounded loop witness is complete exactly when it is both sound and covering for
    the extensional loop-region behavior. -/
theorem loopWitnessComplete_of_sound_and_unrollBound
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (body : List (Block Reg)) (K : Nat)
    (hsound : LoopWitnessSound spec body K)
    (hbound : LoopUnrollBound spec body K) :
    LoopWitnessComplete spec body K := by
  intro s o
  constructor
  · exact hsound s o
  · exact hbound s o

/-- The pair of soundness and coverage assumptions is equivalent to loop witness
    completeness. -/
theorem loopWitnessComplete_iff_sound_and_unrollBound
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (body : List (Block Reg)) (K : Nat) :
    LoopWitnessComplete spec body K ↔
      LoopWitnessSound spec body K ∧ LoopUnrollBound spec body K := by
  constructor
  · intro hcomplete
    refine ⟨?_, ?_⟩
    · intro s o hExec
      exact (hcomplete s o).mp hExec
    · intro s o hDenotes
      exact (hcomplete s o).mpr hDenotes
  · rintro ⟨hsound, hbound⟩
    exact loopWitnessComplete_of_sound_and_unrollBound spec body K hsound hbound

 end VexISA
