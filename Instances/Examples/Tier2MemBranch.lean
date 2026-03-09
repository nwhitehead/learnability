import SymExec.Refinement
import Instances.Examples.Tier0Increment
import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Tier2MemBranch

abbrev Reg := Instances.Examples.ToyReg

/-- Minimal memory-sensitive two-path block: read from memory and branch on a magic byte. -/
def block : Block Reg :=
  { stmts := [Stmt.wrTmp 0 (.load64 (.get .r0)),
              Stmt.exit (.eq64 (.tmp 0) (.const 0x50)) 0x2000]
    ip_reg := .r1
    next := 0 }

def expectedTaken : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 0x2000)
    pc := .and .true (.eq (.load64 .base (.reg .r0)) (.const 0x50)) }

def expectedContinue : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 0)
    pc := .and .true (.not (.eq (.load64 .base (.reg .r0)) (.const 0x50))) }

def expectedPathTaken : Summary Reg :=
  Summary.compose expectedTaken Summary.id

def expectedPathContinue : Summary Reg :=
  Summary.compose expectedContinue Summary.id

def bodyPaths : Finset (List (Block Reg)) := {[block]}

def closure : Finset (SymPC Reg) := {expectedPathTaken.pc, expectedPathContinue.pc}

def behavior (s s' : ConcreteState Reg) : Prop :=
  s' ∈ execBlockPath [block] s

private theorem lowerBlockSummaries_eq_expected :
    lowerBlockSummaries block = {expectedTaken, expectedContinue} := by
  native_decide

private theorem bodyBranchModel_eq_expected :
    bodyBranchModel bodyPaths = {summaryAsBranch expectedPathTaken, summaryAsBranch expectedPathContinue} := by
  native_decide

example : lowerBlockSummaries block = {expectedTaken, expectedContinue} :=
  lowerBlockSummaries_eq_expected

example : bodyBranchModel bodyPaths = {summaryAsBranch expectedPathTaken, summaryAsBranch expectedPathContinue} :=
  bodyBranchModel_eq_expected

private theorem h_contains : ∀ b ∈ bodyBranchModel bodyPaths, b.pc ∈ closure := by
  intro b hb
  have hb' : b = summaryAsBranch expectedPathTaken ∨ b = summaryAsBranch expectedPathContinue := by
    simpa [bodyBranchModel_eq_expected, Finset.mem_insert, Finset.mem_singleton] using hb
  rcases hb' with rfl | rfl <;> simp [closure]

private theorem taken_taken_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathTaken.sub expectedPathTaken.pc = expectedPathTaken.pc := by
  native_decide

private theorem taken_continue_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathTaken.sub expectedPathContinue.pc = expectedPathContinue.pc := by
  native_decide

private theorem continue_taken_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathContinue.sub expectedPathTaken.pc = expectedPathTaken.pc := by
  native_decide

private theorem continue_continue_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathContinue.sub expectedPathContinue.pc = expectedPathContinue.pc := by
  native_decide

private theorem h_semClosed :
    SemClosed (vexSummaryISA Reg) (bodyBranchModel bodyPaths) closure := by
  intro b hb φ hφ s₁ s₂ hEquiv
  have hb' : b = summaryAsBranch expectedPathTaken ∨ b = summaryAsBranch expectedPathContinue := by
    simpa [bodyBranchModel_eq_expected, Finset.mem_insert, Finset.mem_singleton] using hb
  have hφ' : φ = expectedPathTaken.pc ∨ φ = expectedPathContinue.pc := by
    simpa [closure, Finset.mem_insert, Finset.mem_singleton] using hφ
  rcases hb' with rfl | rfl
  · rcases hφ' with rfl | rfl
    · simpa [taken_taken_lift_pc] using hEquiv expectedPathTaken.pc (by simp [closure])
    · simpa [taken_continue_lift_pc] using hEquiv expectedPathContinue.pc (by simp [closure])
  · rcases hφ' with rfl | rfl
    · simpa [continue_taken_lift_pc] using hEquiv expectedPathTaken.pc (by simp [closure])
    · simpa [continue_continue_lift_pc] using hEquiv expectedPathContinue.pc (by simp [closure])

private theorem h_sound :
    BranchModel.Sound (vexSummaryISA Reg)
      (↑(bodyBranchModel bodyPaths) : Set (Branch (SymSub Reg) (SymPC Reg)))
      behavior := by
  intro b hb s hsat
  rcases Finset.mem_image.mp (by simpa [bodyPaths, bodyBranchModel, lowerPathFamilySummaries] using hb) with
    ⟨summary, hSummary, rfl⟩
  have hEnabled : Summary.enabled summary s := by
    simpa [summaryAsBranch, vexSummaryISA, satisfiesSymPC] using hsat
  have hMemSucc : Summary.apply summary s ∈ summarySuccs (lowerBlockPathSummaries [block]) s := by
    exact (mem_summarySuccs (lowerBlockPathSummaries [block]) s (Summary.apply summary s)).2
      ⟨summary, hSummary, hEnabled, rfl⟩
  simpa [behavior, summaryAsBranch, vexSummaryISA,
    summarySuccs_lowerBlockPathSummaries_eq_execBlockPath [block] s] using hMemSucc

private theorem h_complete :
    BranchModel.Complete (vexSummaryISA Reg)
      (↑(bodyBranchModel bodyPaths) : Set (Branch (SymSub Reg) (SymPC Reg)))
      behavior := by
  intro s s' hs'
  have hMemSucc : s' ∈ summarySuccs (lowerBlockPathSummaries [block]) s := by
    simpa [behavior, summarySuccs_lowerBlockPathSummaries_eq_execBlockPath [block] s] using hs'
  rcases (mem_summarySuccs (lowerBlockPathSummaries [block]) s s').1 hMemSucc with
    ⟨summary, hSummary, hEnabled, hApply⟩
  refine ⟨summaryAsBranch summary, ?_, ?_, ?_⟩
  · exact Finset.mem_coe.mpr <| by
      simpa [bodyPaths, bodyBranchModel, lowerPathFamilySummaries] using
        (Finset.mem_image.mpr ⟨summary, hSummary, rfl⟩ :
          summaryAsBranch summary ∈ (lowerBlockPathSummaries [block]).image summaryAsBranch)
  · simpa [summaryAsBranch, vexSummaryISA, satisfiesSymPC] using hEnabled
  · simpa [summaryAsBranch, vexSummaryISA] using hApply

example :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith (vexSummaryISA Reg) closure))
      behavior
      (abstractBehaviorWith (vexSummaryISA Reg) (bodyBranchModel bodyPaths) closure) := by
  exact quotient_bisimulationSem (vexSummaryISA Reg)
    (bodyBranchModel bodyPaths) closure h_contains h_semClosed behavior h_sound h_complete

end Instances.Examples.Tier2MemBranch
