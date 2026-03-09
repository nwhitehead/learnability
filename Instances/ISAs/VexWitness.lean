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

/-- Finite path-family witness for at-most-`K` iterations when each iteration may pick
    any body path from `bodyPaths`. Shorter prefixes remain included at every depth. -/
def branchingLoopWitness
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyPaths : Finset (List (Block Reg))) : Nat → Finset (List (Block Reg))
  | 0 => {[]}
  | n + 1 =>
      branchingLoopWitness bodyPaths n ∪
        bodyPaths.biUnion (fun body =>
          (branchingLoopWitness bodyPaths n).image (fun tail => body ++ tail))

@[simp] theorem branchingLoopWitness_zero
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyPaths : Finset (List (Block Reg))) :
    branchingLoopWitness bodyPaths 0 = {[]} := rfl

@[simp] theorem branchingLoopWitness_succ
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyPaths : Finset (List (Block Reg))) (n : Nat) :
    branchingLoopWitness bodyPaths (n + 1) =
      branchingLoopWitness bodyPaths n ∪
        bodyPaths.biUnion (fun body =>
          (branchingLoopWitness bodyPaths n).image (fun tail => body ++ tail)) := rfl

theorem nil_mem_branchingLoopWitness
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyPaths : Finset (List (Block Reg))) (K : Nat) :
    [] ∈ branchingLoopWitness bodyPaths K := by
  induction K with
  | zero =>
      simp [branchingLoopWitness]
  | succ n ih =>
      exact Finset.mem_union.mpr (Or.inl ih)

theorem cons_mem_branchingLoopWitness
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {bodyPaths : Finset (List (Block Reg))}
    {body tail : List (Block Reg)} {n : Nat}
    (hbody : body ∈ bodyPaths)
    (htail : tail ∈ branchingLoopWitness bodyPaths n) :
    body ++ tail ∈ branchingLoopWitness bodyPaths (n + 1) := by
  rw [branchingLoopWitness_succ]
  exact Finset.mem_union.mpr <| Or.inr <|
    Finset.mem_biUnion.mpr ⟨body, hbody, Finset.mem_image.mpr ⟨tail, htail, rfl⟩⟩

theorem branchingLoopWitness_mono
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyPaths : Finset (List (Block Reg))) :
    ∀ n, branchingLoopWitness bodyPaths n ⊆ branchingLoopWitness bodyPaths (n + 1) := by
  intro n path hpath
  rw [branchingLoopWitness_succ]
  exact Finset.mem_union.mpr (Or.inl hpath)

theorem branchingLoopWitness_mono'
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyPaths : Finset (List (Block Reg))) :
    ∀ {n m}, n ≤ m →
      branchingLoopWitness bodyPaths n ⊆ branchingLoopWitness bodyPaths m := by
  intro n m hnm
  induction hnm with
  | refl =>
      exact Finset.Subset.refl _
  | @step m hnm ih =>
      exact Finset.Subset.trans ih (branchingLoopWitness_mono bodyPaths m)

/-- A branching loop witness is complete when the at-most-`K` family of
    branch-sensitive body-path concatenations covers exactly the loop region. -/
def BranchingLoopWitnessComplete
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (bodyPaths : Finset (List (Block Reg))) (K : Nat) : Prop :=
  WitnessComplete (LoopRegion spec) (branchingLoopWitness bodyPaths K)

/-- Soundness half of the branching witness completeness story. -/
def BranchingLoopWitnessSound
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (bodyPaths : Finset (List (Block Reg))) (K : Nat) : Prop :=
  ∀ s o,
    ExecPathFamilyDenotesObs spec.Relevant spec.observe
      (branchingLoopWitness bodyPaths K) s o →
        spec.DenotesObs s o

/-- Coverage half of the branching witness completeness story. -/
def BranchingLoopUnrollBound
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (bodyPaths : Finset (List (Block Reg))) (K : Nat) : Prop :=
  ∀ s o,
    spec.DenotesObs s o →
      ExecPathFamilyDenotesObs spec.Relevant spec.observe
        (branchingLoopWitness bodyPaths K) s o

/-- Concrete while-loop specialization of the branching coverage obligation. -/
abbrev WhileBranchingLoopUnrollBound
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (summary : VexLoopSummary Reg)
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (bodyPaths : Finset (List (Block Reg))) (K : Nat) : Prop :=
  BranchingLoopUnrollBound
    (whileLoopRegionSpec program ip_reg summary Relevant observe)
    bodyPaths K

theorem branchingLoopWitnessComplete_of_sound_and_unrollBound
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (bodyPaths : Finset (List (Block Reg))) (K : Nat)
    (hsound : BranchingLoopWitnessSound spec bodyPaths K)
    (hbound : BranchingLoopUnrollBound spec bodyPaths K) :
    BranchingLoopWitnessComplete spec bodyPaths K := by
  intro s o
  constructor
  · exact hsound s o
  · exact hbound s o

theorem branchingLoopWitnessComplete_iff_sound_and_unrollBound
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (spec : LoopRegionSpec Reg Obs)
    (bodyPaths : Finset (List (Block Reg))) (K : Nat) :
    BranchingLoopWitnessComplete spec bodyPaths K ↔
      BranchingLoopWitnessSound spec bodyPaths K ∧
        BranchingLoopUnrollBound spec bodyPaths K := by
  constructor
  · intro hcomplete
    refine ⟨?_, ?_⟩
    · intro s o hExec
      exact (hcomplete s o).mp hExec
    · intro s o hDenotes
      exact (hcomplete s o).mpr hDenotes
  · rintro ⟨hsound, hbound⟩
    exact branchingLoopWitnessComplete_of_sound_and_unrollBound
      spec bodyPaths K hsound hbound

/-- Reinterpret a VEX summary as a generic branch so the quotient machinery from
    `SymExec/Quotient.lean` can be reused directly. -/
def summaryAsBranch
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : Summary Reg) : Branch (SymSub Reg) (SymPC Reg) :=
  { sub := summary.sub
    pc := summary.pc }

@[simp] theorem summaryAsBranch_sub
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : Summary Reg) :
    (summaryAsBranch summary).sub = summary.sub := rfl

@[simp] theorem summaryAsBranch_pc
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : Summary Reg) :
    (summaryAsBranch summary).pc = summary.pc := rfl

/-- A pure guard branch for lifting loop-control PCs into the quotient model. -/
def guardBranch
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (pc : SymPC Reg) : Branch (SymSub Reg) (SymPC Reg) :=
  { sub := SymSub.id
    pc := pc }

/-- The symbolic model used for PC-equivalence on the branching-witness route:
    all summaries reachable from the chosen body paths, plus the continue/exit guards. -/
def branchingLoopModel
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : VexLoopSummary Reg)
    (bodyPaths : Finset (List (Block Reg))) :
    Finset (Branch (SymSub Reg) (SymPC Reg)) :=
  (lowerPathFamilySummaries bodyPaths).image summaryAsBranch ∪
    {guardBranch summary.continues, guardBranch summary.exits}

theorem summaryAsBranch_mem_branchingLoopModel
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : VexLoopSummary Reg)
    {bodyPaths : Finset (List (Block Reg))}
    {path : List (Block Reg)} {σ : Summary Reg}
    (hpath : path ∈ bodyPaths)
    (hσ : σ ∈ lowerBlockPathSummaries path) :
    summaryAsBranch σ ∈ branchingLoopModel summary bodyPaths := by
  refine Finset.mem_union.mpr (Or.inl ?_)
  refine Finset.mem_image.mpr ?_
  refine ⟨σ, ?_, rfl⟩
  exact Finset.mem_biUnion.mpr ⟨path, hpath, hσ⟩

theorem continues_mem_branchingLoopModel
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : VexLoopSummary Reg)
    (bodyPaths : Finset (List (Block Reg))) :
    guardBranch summary.continues ∈ branchingLoopModel summary bodyPaths := by
  refine Finset.mem_union.mpr (Or.inr ?_)
  simp [guardBranch]

theorem exits_mem_branchingLoopModel
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : VexLoopSummary Reg)
    (bodyPaths : Finset (List (Block Reg))) :
    guardBranch summary.exits ∈ branchingLoopModel summary bodyPaths := by
  refine Finset.mem_union.mpr (Or.inr ?_)
  simp [guardBranch]

/-- One live branch class = one chosen concrete body path, one symbolic summary from
    that path, and one incoming PC-signature class for the loop model. -/
structure LiveBranchClass (Reg : Type) [DecidableEq Reg] [Fintype Reg] where
  path : List (Block Reg)
  summary : Summary Reg
  signature : Finset (SymPC Reg)

section BranchClassCompression

variable {Reg : Type} {Obs : Type}
variable [DecidableEq Reg] [Fintype Reg]
variable [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
  Decidable ((vexSummaryISA Reg).satisfies s φ)]

/-- A live class is realized at `s` when its path is available, its summary is one of the
    lowered summaries for that path, the summary fires at `s`, and `s` has the recorded
    PC-signature in the loop model. -/
noncomputable def LiveBranchClass.Realizes
    (bodyPaths : Finset (List (Block Reg)))
    (closure : Finset (SymPC Reg))
    (cls : LiveBranchClass Reg)
    (s : ConcreteState Reg) : Prop :=
  cls.path ∈ bodyPaths ∧
    cls.summary ∈ lowerBlockPathSummaries cls.path ∧
    Summary.enabled cls.summary s ∧
    pcSignatureWith (vexSummaryISA Reg) closure s = cls.signature

/-- A realized live class tracks the actual deterministic body step and one concrete path
    that executes that step. This is the explicit symbolic-to-concrete bridge hypothesis. -/
noncomputable def LiveBranchClass.RealizesBodyStep
    (loop : VexLoopSummary Reg)
    (bodyPaths : Finset (List (Block Reg)))
    (closure : Finset (SymPC Reg))
    (cls : LiveBranchClass Reg)
    (s : ConcreteState Reg) : Prop :=
  cls.Realizes bodyPaths closure s ∧
    Summary.apply cls.summary s = loop.bodyEffect s ∧
    loop.bodyEffect s ∈ execBlockPath cls.path s

/-- Every concrete body step admits a representative live class from `bodyPaths`. -/
noncomputable def BodyPathStepRealizable
    (loop : VexLoopSummary Reg)
    (bodyPaths : Finset (List (Block Reg)))
    (closure : Finset (SymPC Reg)) : Prop :=
  ∀ s, ∃ cls : LiveBranchClass Reg, cls.RealizesBodyStep loop bodyPaths closure s

/-- No new live branch classes appear after `K`: every class used after `K` was already
    realized at some iteration `≤ K` on the same concrete orbit. -/
noncomputable def BranchClassesStable
    (loop : VexLoopSummary Reg)
    (bodyPaths : Finset (List (Block Reg)))
    (closure : Finset (SymPC Reg)) (K : Nat) : Prop :=
  ∀ s n, K < n →
    ∃ cls : LiveBranchClass Reg, ∃ m, m ≤ K ∧
      cls.RealizesBodyStep loop bodyPaths closure (loop.bodyEffect^[n] s) ∧
      cls.RealizesBodyStep loop bodyPaths closure (loop.bodyEffect^[m] s)

/-- The loop observation only depends on the PC-equivalence class induced by the chosen
    body-path summaries and loop guards. -/
noncomputable def PCObserveInvariant
    (closure : Finset (SymPC Reg))
    (observe : ConcreteState Reg → Obs) : Prop :=
  ∀ {s₁ s₂},
    (pcSetoidWith (vexSummaryISA Reg) closure).r s₁ s₂ →
      observe s₁ = observe s₂

theorem LiveBranchClass.pcEquiv_of_realizes
    {bodyPaths : Finset (List (Block Reg))}
    {closure : Finset (SymPC Reg)}
    {cls : LiveBranchClass Reg}
    {s₁ s₂ : ConcreteState Reg}
    (h₁ : cls.Realizes bodyPaths closure s₁)
    (h₂ : cls.Realizes bodyPaths closure s₂) :
    (pcSetoidWith (vexSummaryISA Reg) closure).r s₁ s₂ := by
  rcases h₁ with ⟨_, _, _, hsig₁⟩
  rcases h₂ with ⟨_, _, _, hsig₂⟩
  exact equiv_of_pcSignature_eqWith (isa := vexSummaryISA Reg)
    (closure := closure) (hsig₁.trans hsig₂.symm)

theorem LiveBranchClass.summary_enabled_of_realizes
    {loop : VexLoopSummary Reg}
    {bodyPaths : Finset (List (Block Reg))}
    {closure : Finset (SymPC Reg)}
    {cls : LiveBranchClass Reg}
    {s₁ s₂ : ConcreteState Reg}
    (h_contains : ∀ b ∈ branchingLoopModel loop bodyPaths, b.pc ∈ closure)
    (h₁ : cls.Realizes bodyPaths closure s₁)
    (h₂ : cls.Realizes bodyPaths closure s₂) :
    Summary.enabled cls.summary s₂ := by
  have hequiv := LiveBranchClass.pcEquiv_of_realizes (cls := cls) h₁ h₂
  rcases h₁ with ⟨hpath, hsummary, henabled, _⟩
  have hmem :
      summaryAsBranch cls.summary ∈ branchingLoopModel loop bodyPaths :=
    summaryAsBranch_mem_branchingLoopModel loop hpath hsummary
  exact pcEquiv_branch_firesWith
    (isa := vexSummaryISA Reg)
    (closure := closure)
    (h_contains _ hmem)
    hequiv
    henabled

theorem LiveBranchClass.successor_pcEquiv_of_realizes
    {loop : VexLoopSummary Reg}
    {bodyPaths : Finset (List (Block Reg))}
    {closure : Finset (SymPC Reg)}
    {cls : LiveBranchClass Reg}
    {s₁ s₂ : ConcreteState Reg}
    (h_closed :
      ∀ b ∈ branchingLoopModel loop bodyPaths, ∀ φ ∈ closure,
        (vexSummaryISA Reg).pc_lift b.sub φ ∈ closure)
    (h₁ : cls.Realizes bodyPaths closure s₁)
    (h₂ : cls.Realizes bodyPaths closure s₂) :
    (pcSetoidWith (vexSummaryISA Reg) closure).r
      (Summary.apply cls.summary s₁)
      (Summary.apply cls.summary s₂) := by
  have hequiv := LiveBranchClass.pcEquiv_of_realizes (cls := cls) h₁ h₂
  rcases h₁ with ⟨hpath, hsummary, _, _⟩
  have hmem :
      summaryAsBranch cls.summary ∈ branchingLoopModel loop bodyPaths :=
    summaryAsBranch_mem_branchingLoopModel loop hpath hsummary
  simpa [Summary.apply, summaryAsBranch] using
    pcEquiv_eval_subWith
      (isa := vexSummaryISA Reg)
      (closure := closure)
      (b := summaryAsBranch cls.summary)
      (fun φ hφ => h_closed _ hmem φ hφ)
      hequiv

/-- Any bounded number of concrete loop iterations is already realized by the branching
    witness, provided each concrete body step has a body-path representative. -/
theorem branchingLoopWitness_reaches_iterate
    (loop : VexLoopSummary Reg)
    (bodyPaths : Finset (List (Block Reg)))
    (closure : Finset (SymPC Reg))
    (hstep : BodyPathStepRealizable loop bodyPaths closure) :
    ∀ n s,
      ∃ blocks ∈ branchingLoopWitness bodyPaths n,
        iterateBody (isa := vexSummaryISA Reg) loop n s ∈ execBlockPath blocks s := by
  intro n
  induction n with
  | zero =>
      intro s
      refine ⟨[], by simp [branchingLoopWitness], ?_⟩
      simp [iterateBody, execBlockPath]
  | succ n ih =>
      intro s
      obtain ⟨cls, hcls⟩ := hstep s
      obtain ⟨tail, htailMem, htailExec⟩ := ih (loop.bodyEffect s)
      rcases hcls with ⟨hreal, happly, hpathExec⟩
      rcases hreal with ⟨hpath, _, _, _⟩
      refine ⟨cls.path ++ tail, cons_mem_branchingLoopWitness hpath htailMem, ?_⟩
      rw [iterateBody_succ (isa := vexSummaryISA Reg) loop n s]
      rw [execBlockPath_append]
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨loop.bodyEffect s, ?_, ?_⟩
      · simpa [happly] using hpathExec
      · exact htailExec

/-- Branch-class stabilization compresses every loop observation into the bounded branching
    witness. The proof uses: repeated live class -> repeated PC signature -> repeated
    loop-control outcome (`pcEquiv_branch_fires`) -> bounded concrete orbit, while
    `pcEquiv_eval_sub` is available as the one-step congruence for downstream tail proofs. -/
theorem whileLoopBranchingUnrollBound_of_branchClassesStable
    (program : Program Reg) (ip_reg : Reg)
    (loop : VexLoopSummary Reg)
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (bodyPaths : Finset (List (Block Reg)))
    (closure : Finset (SymPC Reg)) (K : Nat)
    (hstep : BodyPathStepRealizable loop bodyPaths closure)
    (hstable : BranchClassesStable loop bodyPaths closure K)
    (hobs : PCObserveInvariant closure observe) :
    WhileBranchingLoopUnrollBound program ip_reg loop Relevant observe bodyPaths K := by
  intro s o hDenotes
  rcases hDenotes with ⟨hRel, s', hWhile, hObs⟩
  rcases hWhile with ⟨n, hIter, hCont, hExit⟩
  simp only [iterateBody] at hIter
  by_cases hn : n ≤ K
  · obtain ⟨blocks, hMem, hExec⟩ :=
      branchingLoopWitness_reaches_iterate loop bodyPaths closure hstep n s
    exact ⟨blocks, branchingLoopWitness_mono' bodyPaths hn hMem,
      ⟨hRel, s', by simpa [hIter.symm] using hExec, hObs⟩⟩
  · push_neg at hn
    obtain ⟨cls, m, hm, hClsN, hClsM⟩ := hstable s n hn
    have hm_lt_n : m < n := by omega
    have hEqvMN :
        (pcSetoidWith (vexSummaryISA Reg) closure).r
          (loop.bodyEffect^[m] s)
          (loop.bodyEffect^[n] s) :=
      LiveBranchClass.pcEquiv_of_realizes (cls := cls) hClsM.1 hClsN.1
    have hObsM : observe (loop.bodyEffect^[m] s) = o := by
      have hEqObs :
          observe (loop.bodyEffect^[m] s) = observe (loop.bodyEffect^[n] s) :=
        hobs hEqvMN
      rw [hIter] at hEqObs
      exact hEqObs.trans hObs
    obtain ⟨blocks, hMem, hExec⟩ :=
      branchingLoopWitness_reaches_iterate loop bodyPaths closure hstep m s
    exact ⟨blocks, branchingLoopWitness_mono' bodyPaths hm hMem,
      ⟨hRel, loop.bodyEffect^[m] s, hExec, hObsM⟩⟩

/-- Packaging theorem: once the branching witness is known sound, branch-class stability
    discharges the missing coverage half and yields witness completeness. -/
theorem whileBranchingLoopWitnessComplete_of_branchClassesStable
    (program : Program Reg) (ip_reg : Reg)
    (loop : VexLoopSummary Reg)
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (bodyPaths : Finset (List (Block Reg)))
    (closure : Finset (SymPC Reg)) (K : Nat)
    (hsound :
      BranchingLoopWitnessSound
        (whileLoopRegionSpec program ip_reg loop Relevant observe)
        bodyPaths K)
    (hstep : BodyPathStepRealizable loop bodyPaths closure)
    (hstable : BranchClassesStable loop bodyPaths closure K)
    (hobs : PCObserveInvariant closure observe) :
    BranchingLoopWitnessComplete
      (whileLoopRegionSpec program ip_reg loop Relevant observe)
      bodyPaths K := by
  apply branchingLoopWitnessComplete_of_sound_and_unrollBound
  · exact hsound
  · exact whileLoopBranchingUnrollBound_of_branchClassesStable
      program ip_reg loop Relevant observe bodyPaths closure K hstep hstable hobs

end BranchClassCompression


/-! ## Bridge to Quotient Bisimulation (STS1)

Connect the VEX witness layer to the general quotient bisimulation framework
from `SymExec/Quotient.lean`. The key bridge: `BodyPathStepRealizable` implies
`BranchModel.Complete` for the body sub-model. -/

section BodyQuotientBridge

variable {Reg : Type}
variable [DecidableEq Reg] [Fintype Reg]
variable [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
  Decidable ((vexSummaryISA Reg).satisfies s φ)]

/-- The body-only sub-model: summaries from body paths, without loop guards. -/
def bodyBranchModel
    (bodyPaths : Finset (List (Block Reg))) :
    Finset (Branch (SymSub Reg) (SymPC Reg)) :=
  (lowerPathFamilySummaries bodyPaths).image summaryAsBranch

set_option linter.unusedSectionVars false in
theorem bodyBranchModel_sub_branchingLoopModel
    (loop : VexLoopSummary Reg)
    (bodyPaths : Finset (List (Block Reg))) :
    bodyBranchModel bodyPaths ⊆ branchingLoopModel loop bodyPaths :=
  fun _ hb => Finset.mem_union.mpr (Or.inl hb)

/-- `BodyPathStepRealizable` implies `BranchModel.Complete` for the bodyEffect
    transition over the body sub-model. This bridges the witness layer into the
    general quotient bisimulation framework from Quotient.lean. -/
theorem bodyEffect_branchComplete
    (loop : VexLoopSummary Reg)
    (bodyPaths : Finset (List (Block Reg)))
    (closure : Finset (SymPC Reg))
    (hstep : BodyPathStepRealizable loop bodyPaths closure) :
    BranchModel.Complete (vexSummaryISA Reg)
      (↑(bodyBranchModel bodyPaths) : Set (Branch (SymSub Reg) (SymPC Reg)))
      (fun s s' => s' = loop.bodyEffect s) := by
  intro s s' hs'
  obtain ⟨cls, ⟨hpath, hsummary, henabled, _⟩, happly, _⟩ := hstep s
  refine ⟨summaryAsBranch cls.summary,
    Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨cls.summary,
      Finset.mem_biUnion.mpr ⟨cls.path, hpath, hsummary⟩, rfl⟩),
    henabled, ?_⟩
  subst hs'; exact happly

/-- The VEX body transition has a finite bisimilarity quotient (STS1).

    Given:
    - A body sub-model that is sound for bodyEffect (every fired branch computes bodyEffect)
    - `BodyPathStepRealizable` (completeness: every body step has a branch witness)
    - Closure properties (model PCs in closure, closure closed under lifting)

    The quotient by PC-equivalence is a cross-system bisimulation with at most
    2^|closure| abstract states. This is HMR05 Theorem 1A for the VEX body. -/
theorem vexBodyQuotientBisimulation
    (loop : VexLoopSummary Reg)
    (bodyPaths : Finset (List (Block Reg)))
    (closure : Finset (SymPC Reg))
    (h_contains : ∀ b ∈ bodyBranchModel bodyPaths, b.pc ∈ closure)
    (h_closed : ∀ b ∈ bodyBranchModel bodyPaths, ∀ φ ∈ closure,
      (vexSummaryISA Reg).pc_lift b.sub φ ∈ closure)
    (hstep : BodyPathStepRealizable loop bodyPaths closure)
    (h_sound : BranchModel.Sound (vexSummaryISA Reg)
      (↑(bodyBranchModel bodyPaths) : Set (Branch (SymSub Reg) (SymPC Reg)))
      (fun s s' => s' = loop.bodyEffect s)) :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith (vexSummaryISA Reg) closure))
      (fun s s' => s' = loop.bodyEffect s)
      (abstractBehaviorWith (vexSummaryISA Reg) (bodyBranchModel bodyPaths) closure) :=
  quotient_bisimulationWith (vexSummaryISA Reg)
    (bodyBranchModel bodyPaths) closure h_contains h_closed
    (fun s s' => s' = loop.bodyEffect s) h_sound
    (bodyEffect_branchComplete loop bodyPaths closure hstep)

/-- The VEX body quotient has at most 2^|closure| abstract states. -/
theorem vexBodyQuotient_card_bound
    (closure : Finset (SymPC Reg)) :
    Fintype.card (Quotient (pcSetoidWith (vexSummaryISA Reg) closure)) ≤
      2 ^ closure.card :=
  abstractStateWith_card_bound (vexSummaryISA Reg) closure

end BodyQuotientBridge

/-- For the concrete while-based loop region, witness soundness follows once every
    repeated body path up to the bound denotes a bounded while execution. This is the
    easy direction: bounded witness behaviors are real loop behaviors. -/
theorem whileLoopWitnessSound_of_boundedPathBehavior
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (summary : VexLoopSummary Reg)
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (body : List (Block Reg)) (K : Nat)
    (hpath :
      ∀ n s s',
        n ≤ K →
        s' ∈ execBlockPath (repeatBlockPath body n) s →
          boundedWhileBehavior (isa := vexSummaryISA Reg) summary K s s') :
    LoopWitnessSound (whileLoopRegionSpec program ip_reg summary Relevant observe) body K := by
  intro s o hExec
  rcases hExec with ⟨blocks, hMem, hBlocks⟩
  rcases (mem_boundedLoopWitness_iff body K blocks).mp hMem with ⟨n, hn, hEq⟩
  subst hEq
  rcases hBlocks with ⟨hRel, s', hPath, hObs⟩
  refine ⟨hRel, s', ?_, hObs⟩
  exact boundedWhileBehavior_implies_whileBehavior summary K (hpath n s s' hn hPath)

/-- If the guard-free loop branch set stabilizes at `K`, then any concrete while-loop
    behavior is bounded by `K` iterations. Combined with a bridge showing that bounded
    while executions are covered by the bounded path-family witness, this discharges the
    concrete `WhileLoopUnrollBound` obligation. -/
theorem whileLoopUnrollBound_of_stabilization
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (summary : VexLoopSummary Reg)
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (body : List (Block Reg)) (K : Nat)
    (h_stab :
      loopBranchSet (isa := vexSummaryISA Reg) summary K =
        loopBranchSet (isa := vexSummaryISA Reg) summary (K + 1))
    (hcover :
      ∀ s s',
        boundedWhileBehavior (isa := vexSummaryISA Reg) summary K s s' →
          ∃ blocks ∈ boundedLoopWitness body K, s' ∈ execBlockPath blocks s) :
    WhileLoopUnrollBound program ip_reg summary Relevant observe body K := by
  intro s o hDenotes
  rcases hDenotes with ⟨hRel, s', hWhile, hObs⟩
  have hBounded :
      boundedWhileBehavior (isa := vexSummaryISA Reg) summary K s s' :=
    stabilization_complete (isa := vexSummaryISA Reg) summary K h_stab s s' hWhile
  rcases hcover s s' hBounded with ⟨blocks, hMem, hPath⟩
  exact ⟨blocks, hMem, ⟨hRel, s', hPath, hObs⟩⟩

/-- If one concrete execution of the VEX body path realizes the loop's `bodyEffect`,
    then repeating that path `n` times realizes the `n`-th iterate of `bodyEffect`. -/
theorem repeatBlockPath_reaches_iterate_of_bodyEffect_mem
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : VexLoopSummary Reg)
    (body : List (Block Reg))
    (hbody : ∀ s, summary.bodyEffect s ∈ execBlockPath body s) :
    ∀ n s,
      summary.bodyEffect^[n] s ∈ execBlockPath (repeatBlockPath body n) s := by
  intro n
  induction n with
  | zero =>
      intro s
      simp [repeatBlockPath, execBlockPath]
  | succ n ih =>
      intro s
      rw [repeatBlockPath_succ, execBlockPath_append]
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨summary.bodyEffect s, hbody s, ?_⟩
      simpa using ih (summary.bodyEffect s)

/-- A single-step body-path realization hypothesis is enough to cover every bounded
    while execution by some path in the bounded loop witness. -/
theorem boundedWhileCoverage_of_bodyEffect_path
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : VexLoopSummary Reg)
    (body : List (Block Reg)) (K : Nat)
    (hbody : ∀ s, summary.bodyEffect s ∈ execBlockPath body s) :
    ∀ s s',
      boundedWhileBehavior (isa := vexSummaryISA Reg) summary K s s' →
        ∃ blocks ∈ boundedLoopWitness body K, s' ∈ execBlockPath blocks s := by
  intro s s' h
  rcases h with ⟨n, hn, hIter, _, _⟩
  refine ⟨repeatBlockPath body n, ?_, ?_⟩
  · exact (mem_boundedLoopWitness_iff body K (repeatBlockPath body n)).2 ⟨n, hn, rfl⟩
  · simpa [hIter.symm] using repeatBlockPath_reaches_iterate_of_bodyEffect_mem summary body hbody n s

/-- Under stabilization, a simple one-step body-path realization hypothesis suffices to
    discharge the concrete while-loop unroll bound. -/
theorem whileLoopUnrollBound_of_stabilization_and_bodyEffect_path
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (summary : VexLoopSummary Reg)
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (body : List (Block Reg)) (K : Nat)
    (h_stab :
      loopBranchSet (isa := vexSummaryISA Reg) summary K =
        loopBranchSet (isa := vexSummaryISA Reg) summary (K + 1))
    (hbody : ∀ s, summary.bodyEffect s ∈ execBlockPath body s) :
    WhileLoopUnrollBound program ip_reg summary Relevant observe body K :=
  whileLoopUnrollBound_of_stabilization program ip_reg summary Relevant observe body K h_stab
    (boundedWhileCoverage_of_bodyEffect_path summary body K hbody)

 end VexISA
