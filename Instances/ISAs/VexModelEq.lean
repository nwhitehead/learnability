import Mathlib.Data.Fintype.Basic
import ModelEq
import Instances.ISAs.VexProgram

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

abbrev VexModelDenotesObs {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (M : Finset (Summary Reg)) (s : ConcreteState Reg) (o : Obs) : Prop :=
  ModelDenotesObs Summary.enabled Summary.apply Relevant observe M s o

abbrev VexSummaryEq {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (a b : Summary Reg) : Prop :=
  SummaryEq Summary.enabled Summary.apply Relevant observe a b

abbrev VexModelEq {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (M N : Finset (Summary Reg)) : Prop :=
  ModelEq Summary.enabled Summary.apply Relevant observe M N

abbrev VexModelEqState {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (M N : Finset (Summary Reg)) : Prop :=
  ModelEqState Summary.enabled Summary.apply Relevant M N

/-- Observation-level denotation of a raw VEX block through its concrete successor set. -/
def ExecBlockDenotesObs {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (block : Block Reg) (s : ConcreteState Reg) (o : Obs) : Prop :=
  Relevant s ∧ ∃ s' ∈ execBlockSuccs block s, observe s' = o

/-- Observation-level denotation of a fixed VEX block path through its concrete successor set. -/
def ExecBlockPathDenotesObs {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (blocks : List (Block Reg)) (s : ConcreteState Reg) (o : Obs) : Prop :=
  Relevant s ∧ ∃ s' ∈ execBlockPath blocks s, observe s' = o

/-- Observation-level denotation of a summary family through its executable successor set. -/
def SummarySuccsDenotesObs {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (summaries : Finset (Summary Reg)) (s : ConcreteState Reg) (o : Obs) : Prop :=
  Relevant s ∧ ∃ s' ∈ summarySuccs summaries s, observe s' = o

theorem vexModelDenotesObs_iff_summarySuccsDenotesObs
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (summaries : Finset (Summary Reg)) (s : ConcreteState Reg) (o : Obs) :
    VexModelDenotesObs Relevant observe summaries s o ↔
      SummarySuccsDenotesObs Relevant observe summaries s o := by
  constructor
  · intro h
    rcases h with ⟨hRel, summary, hMem, hEnabled, hObs⟩
    refine ⟨hRel, Summary.apply summary s, ?_, hObs⟩
    exact (mem_summarySuccs summaries s (Summary.apply summary s)).2 ⟨summary, hMem, hEnabled, rfl⟩
  · intro h
    rcases h with ⟨hRel, s', hMem, hObs⟩
    rcases (mem_summarySuccs summaries s s').1 hMem with ⟨summary, hSummary, hEnabled, hApply⟩
    exact ⟨hRel, summary, hSummary, hEnabled, by simpa [hApply] using hObs⟩

theorem vexModelEq_insert_dead
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (M : Finset (Summary Reg)) (b : Summary Reg)
    (hdead : ∀ s, Relevant s → ¬ Summary.enabled b s) :
    VexModelEq Relevant observe (insert b M) M :=
  modelEq_insert_dead Summary.enabled Summary.apply Relevant observe M b hdead

theorem vexModelEqState_implies_vexModelEq
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    {M N : Finset (Summary Reg)}
    (h : VexModelEqState Relevant M N) :
    VexModelEq Relevant observe M N :=
  modelEqState_implies_modelEq Summary.enabled Summary.apply Relevant observe h

theorem lowerBlockSummaries_denotesObs_iff_execBlock
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (block : Block Reg) (s : ConcreteState Reg) (o : Obs) :
    VexModelDenotesObs Relevant observe (lowerBlockSummaries block) s o ↔
      ExecBlockDenotesObs Relevant observe block s o := by
  rw [vexModelDenotesObs_iff_summarySuccsDenotesObs]
  constructor
  · rintro ⟨hRel, sOut, hMem, hObs⟩
    exact ⟨hRel, sOut, by simpa [summarySuccs_lowerBlockSummaries_eq_execBlockSuccs block s] using hMem, hObs⟩
  · rintro ⟨hRel, sOut, hMem, hObs⟩
    exact ⟨hRel, sOut, by simpa [summarySuccs_lowerBlockSummaries_eq_execBlockSuccs block s] using hMem, hObs⟩

theorem lowerBlockPathSummaries_denotesObs_iff_execBlockPath
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (blocks : List (Block Reg)) (s : ConcreteState Reg) (o : Obs) :
    VexModelDenotesObs Relevant observe (lowerBlockPathSummaries blocks) s o ↔
      ExecBlockPathDenotesObs Relevant observe blocks s o := by
  rw [vexModelDenotesObs_iff_summarySuccsDenotesObs]
  constructor
  · rintro ⟨hRel, sOut, hMem, hObs⟩
    exact ⟨hRel, sOut, by simpa [summarySuccs_lowerBlockPathSummaries_eq_execBlockPath blocks s] using hMem, hObs⟩
  · rintro ⟨hRel, sOut, hMem, hObs⟩
    exact ⟨hRel, sOut, by simpa [summarySuccs_lowerBlockPathSummaries_eq_execBlockPath blocks s] using hMem, hObs⟩

theorem lowerBlockSummaries_denotesState_iff_execBlock
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (block : Block Reg) (s s' : ConcreteState Reg) :
    VexModelDenotesObs Relevant (fun state => state) (lowerBlockSummaries block) s s' ↔
      (Relevant s ∧ s' ∈ execBlockSuccs block s) := by
  simpa [ExecBlockDenotesObs] using
    (lowerBlockSummaries_denotesObs_iff_execBlock Relevant (fun state => state) block s s')

theorem lowerBlockPathSummaries_denotesState_iff_execBlockPath
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (blocks : List (Block Reg)) (s s' : ConcreteState Reg) :
    VexModelDenotesObs Relevant (fun state => state) (lowerBlockPathSummaries blocks) s s' ↔
      (Relevant s ∧ s' ∈ execBlockPath blocks s) := by
  simpa [ExecBlockPathDenotesObs] using
    (lowerBlockPathSummaries_denotesObs_iff_execBlockPath Relevant (fun state => state) blocks s s')

/-- A fixed lifted VEX block path is extractible as an observation-level model when its
    lowered summary family and concrete execution induce the same observed behavior on
    all relevant inputs. -/
def ExtractiblePathModel
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (blocks : List (Block Reg)) : Prop :=
  ∀ s o,
    VexModelDenotesObs Relevant observe (lowerBlockPathSummaries blocks) s o ↔
      ExecBlockPathDenotesObs Relevant observe blocks s o

/-- Lowered summary families are semantically adequate observation-level models of fixed
    lifted VEX block paths. -/
theorem extractiblePathModel_of_lowering
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (blocks : List (Block Reg)) :
    ExtractiblePathModel Relevant observe blocks := by
  intro s o
  exact lowerBlockPathSummaries_denotesObs_iff_execBlockPath Relevant observe blocks s o

theorem composeLowerBlockPathSummaries_denotesState_iff_execBlockPath_append
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (blocks₁ blocks₂ : List (Block Reg)) (s s' : ConcreteState Reg) :
    VexModelDenotesObs Relevant (fun state => state)
        (composeSummaryFinsets (lowerBlockPathSummaries blocks₁) (lowerBlockPathSummaries blocks₂)) s s' ↔
      (Relevant s ∧ s' ∈ execBlockPath (blocks₁ ++ blocks₂) s) := by
  rw [vexModelDenotesObs_iff_summarySuccsDenotesObs]
  constructor
  · rintro ⟨hRel, out, hMem, hEq⟩
    subst hEq
    exact ⟨hRel, by simpa [summarySuccs_composeLowerBlockPathSummaries_eq_execBlockPath_append blocks₁ blocks₂ s] using hMem⟩
  · rintro ⟨hRel, hMem⟩
    exact ⟨hRel, s', by simpa [summarySuccs_composeLowerBlockPathSummaries_eq_execBlockPath_append blocks₁ blocks₂ s] using hMem, rfl⟩

/-- Path extraction commutes with composition at the strongest state-level model equivalence. -/
theorem lowerBlockPathSummaries_append_modelEqState
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (blocks₁ blocks₂ : List (Block Reg)) :
    VexModelEqState Relevant
      (composeSummaryFinsets (lowerBlockPathSummaries blocks₁) (lowerBlockPathSummaries blocks₂))
      (lowerBlockPathSummaries (blocks₁ ++ blocks₂)) := by
  intro s s'
  exact Iff.trans
    (by
      simpa using
        (composeLowerBlockPathSummaries_denotesState_iff_execBlockPath_append Relevant blocks₁ blocks₂ s s'))
    (by
      simpa using
        (lowerBlockPathSummaries_denotesState_iff_execBlockPath Relevant (blocks₁ ++ blocks₂) s s').symm)

/-- Path extraction commutes with composition up to observation-level model equivalence. -/
theorem extractiblePathModel_compose
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (blocks₁ blocks₂ : List (Block Reg)) :
    VexModelEq Relevant observe
      (composeSummaryFinsets (lowerBlockPathSummaries blocks₁) (lowerBlockPathSummaries blocks₂))
      (lowerBlockPathSummaries (blocks₁ ++ blocks₂)) :=
  vexModelEqState_implies_vexModelEq Relevant observe
    (lowerBlockPathSummaries_append_modelEqState Relevant blocks₁ blocks₂)

/-- Observation-level denotation of one concrete fetched-block program step. -/
def ExecProgramStepDenotesObs
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (program : Program Reg) (ip_reg : Reg)
    (s : ConcreteState Reg) (o : Obs) : Prop :=
  Relevant s ∧ ∃ s', ProgramStep program ip_reg s s' ∧ observe s' = o

/-- Observation-level denotation of one lowered-summary fetched-block program step. -/
def SummaryProgramStepDenotesObs
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (program : Program Reg) (ip_reg : Reg)
    (s : ConcreteState Reg) (o : Obs) : Prop :=
  Relevant s ∧ ∃ s', ProgramSummaryStep program ip_reg s s' ∧ observe s' = o

/-- One fetched-block program step is observation-level extractible when the concrete
    and lowered-summary step relations induce the same observed behavior on all relevant inputs. -/
def ExtractibleProgramStep
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (program : Program Reg) (ip_reg : Reg) : Prop :=
  ∀ s o,
    SummaryProgramStepDenotesObs Relevant observe program ip_reg s o ↔
      ExecProgramStepDenotesObs Relevant observe program ip_reg s o

theorem summaryProgramStepDenotesObs_iff_execProgramStep
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (program : Program Reg) (ip_reg : Reg)
    (s : ConcreteState Reg) (o : Obs) :
    SummaryProgramStepDenotesObs Relevant observe program ip_reg s o ↔
      ExecProgramStepDenotesObs Relevant observe program ip_reg s o := by
  constructor
  · rintro ⟨hRel, sOut, hStep, hObs⟩
    exact ⟨hRel, sOut, (programStep_iff_summaryStep program ip_reg s sOut).mpr hStep, hObs⟩
  · rintro ⟨hRel, sOut, hStep, hObs⟩
    exact ⟨hRel, sOut, (programStep_iff_summaryStep program ip_reg s sOut).mp hStep, hObs⟩

/-- Lowered-summary one-step fetched-block execution is an observation-level adequate
    model of concrete fetched-block program stepping. -/
theorem extractibleProgramStep_of_lowering
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (program : Program Reg) (ip_reg : Reg) :
    ExtractibleProgramStep Relevant observe program ip_reg := by
  intro s o
  exact summaryProgramStepDenotesObs_iff_execProgramStep Relevant observe program ip_reg s o

theorem summaryProgramStepDenotesState_iff_execProgramStep
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (program : Program Reg) (ip_reg : Reg)
    (s sOut : ConcreteState Reg) :
    SummaryProgramStepDenotesObs Relevant (fun state => state) program ip_reg s sOut ↔
      (Relevant s ∧ ProgramStep program ip_reg s sOut) := by
  constructor
  · rintro ⟨hRel, out, hStep, hEq⟩
    have hStep' : ProgramStep program ip_reg s out :=
      (programStep_iff_summaryStep program ip_reg s out).mpr hStep
    subst hEq
    exact ⟨hRel, hStep'⟩
  · rintro ⟨hRel, hStep⟩
    exact ⟨hRel, sOut, (programStep_iff_summaryStep program ip_reg s sOut).mp hStep, rfl⟩

end VexISA
