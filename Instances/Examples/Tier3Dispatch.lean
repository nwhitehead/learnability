import SymExec.Refinement
import Instances.Examples.Tier0Increment
import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Tier3Dispatch

abbrev Reg := Instances.Examples.ToyReg

/-- Minimal three-path dispatch block: inspect a loaded value and route to two magic targets. -/
def block : Block Reg :=
  { stmts := [Stmt.wrTmp 0 (.load64 (.get .r0)),
              Stmt.exit (.eq64 (.tmp 0) (.const 0x50)) 0x3000,
              Stmt.exit (.eq64 (.tmp 0) (.const 0x47)) 0x4000]
    ip_reg := .r1
    next := 0 }

def condP : SymPC Reg :=
  .eq (.load64 .base (.reg .r0)) (.const 0x50)

def condG : SymPC Reg :=
  .eq (.load64 .base (.reg .r0)) (.const 0x47)

def expectedP : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 0x3000)
    pc := .and .true condP }

def expectedG : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 0x4000)
    pc := .and (.and .true (.not condP)) condG }

def expectedOther : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 0)
    pc := .and (.and .true (.not condP)) (.not condG) }

def expectedPathP : Summary Reg := Summary.compose expectedP Summary.id
def expectedPathG : Summary Reg := Summary.compose expectedG Summary.id
def expectedPathOther : Summary Reg := Summary.compose expectedOther Summary.id

def bodyPaths : Finset (List (Block Reg)) := {[block]}

def closure : Finset (SymPC Reg) := {expectedPathP.pc, expectedPathG.pc, expectedPathOther.pc}

def behavior (s s' : ConcreteState Reg) : Prop :=
  s' ∈ execBlockPath [block] s

private theorem lowerBlockSummaries_eq_expected :
    lowerBlockSummaries block = {expectedP, expectedG, expectedOther} := by
  native_decide

private theorem bodyBranchModel_eq_expected :
    bodyBranchModel bodyPaths =
      {summaryAsBranch expectedPathP, summaryAsBranch expectedPathG, summaryAsBranch expectedPathOther} := by
  native_decide

example : lowerBlockSummaries block = {expectedP, expectedG, expectedOther} :=
  lowerBlockSummaries_eq_expected

example :
    bodyBranchModel bodyPaths =
      {summaryAsBranch expectedPathP, summaryAsBranch expectedPathG, summaryAsBranch expectedPathOther} :=
  bodyBranchModel_eq_expected

private theorem h_contains : ∀ b ∈ bodyBranchModel bodyPaths, b.pc ∈ closure := by
  intro b hb
  have hb' :
      b = summaryAsBranch expectedPathP ∨
        b = summaryAsBranch expectedPathG ∨
        b = summaryAsBranch expectedPathOther := by
    simpa [bodyBranchModel_eq_expected, Finset.mem_insert, Finset.mem_singleton] using hb
  rcases hb' with rfl | hrest
  · simp [closure]
  · rcases hrest with rfl | rfl <;> simp [closure]

private theorem p_p_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathP.sub expectedPathP.pc = expectedPathP.pc := by
  native_decide

private theorem p_g_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathP.sub expectedPathG.pc = expectedPathG.pc := by
  native_decide

private theorem p_other_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathP.sub expectedPathOther.pc = expectedPathOther.pc := by
  native_decide

private theorem g_p_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathG.sub expectedPathP.pc = expectedPathP.pc := by
  native_decide

private theorem g_g_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathG.sub expectedPathG.pc = expectedPathG.pc := by
  native_decide

private theorem g_other_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathG.sub expectedPathOther.pc = expectedPathOther.pc := by
  native_decide

private theorem other_p_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathOther.sub expectedPathP.pc = expectedPathP.pc := by
  native_decide

private theorem other_g_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathOther.sub expectedPathG.pc = expectedPathG.pc := by
  native_decide

private theorem other_other_lift_pc :
    (vexSummaryISA Reg).pc_lift expectedPathOther.sub expectedPathOther.pc = expectedPathOther.pc := by
  native_decide

private theorem h_semClosed :
    SemClosed (vexSummaryISA Reg) (bodyBranchModel bodyPaths) closure := by
  intro b hb φ hφ s₁ s₂ hEquiv
  have hb' :
      b = summaryAsBranch expectedPathP ∨
        b = summaryAsBranch expectedPathG ∨
        b = summaryAsBranch expectedPathOther := by
    simpa [bodyBranchModel_eq_expected, Finset.mem_insert, Finset.mem_singleton] using hb
  have hφ' :
      φ = expectedPathP.pc ∨ φ = expectedPathG.pc ∨ φ = expectedPathOther.pc := by
    simpa [closure, Finset.mem_insert, Finset.mem_singleton] using hφ
  rcases hb' with rfl | hb'
  · rcases hφ' with rfl | hφ'
    · simpa [p_p_lift_pc] using hEquiv expectedPathP.pc (by simp [closure])
    · rcases hφ' with rfl | rfl
      · simpa [p_g_lift_pc] using hEquiv expectedPathG.pc (by simp [closure])
      · simpa [p_other_lift_pc] using hEquiv expectedPathOther.pc (by simp [closure])
  · rcases hb' with rfl | rfl
    · rcases hφ' with rfl | hφ'
      · simpa [g_p_lift_pc] using hEquiv expectedPathP.pc (by simp [closure])
      · rcases hφ' with rfl | rfl
        · simpa [g_g_lift_pc] using hEquiv expectedPathG.pc (by simp [closure])
        · simpa [g_other_lift_pc] using hEquiv expectedPathOther.pc (by simp [closure])
    · rcases hφ' with rfl | hφ'
      · simpa [other_p_lift_pc] using hEquiv expectedPathP.pc (by simp [closure])
      · rcases hφ' with rfl | rfl
        · simpa [other_g_lift_pc] using hEquiv expectedPathG.pc (by simp [closure])
        · simpa [other_other_lift_pc] using hEquiv expectedPathOther.pc (by simp [closure])

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

end Instances.Examples.Tier3Dispatch
