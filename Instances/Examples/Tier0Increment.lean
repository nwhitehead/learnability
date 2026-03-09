import SymExec.Refinement
import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples

inductive ToyReg where
  | r0
  | r1
  deriving DecidableEq, Repr

instance : Fintype ToyReg where
  elems := {ToyReg.r0, ToyReg.r1}
  complete := by
    intro r
    cases r <;> simp

def block : Block ToyReg :=
  { stmts := [Stmt.put .r0 (.add64 (.get .r0) (.const 1))]
    ip_reg := .r1
    next := 0 }

def expectedSummary : Summary ToyReg :=
  { sub := SymSub.write (SymSub.write SymSub.id .r0 (.add64 (.reg .r0) (.const 1))) .r1 (.const 0)
    pc := .true }

def expectedPathSummary : Summary ToyReg :=
  Summary.compose expectedSummary Summary.id

def bodyPaths : Finset (List (Block ToyReg)) := {[block]}

def closure : Finset (SymPC ToyReg) := {expectedPathSummary.pc}

def behavior (s s' : ConcreteState ToyReg) : Prop :=
  s' = execBlock block s

private theorem lowerBlockSummaries_eq_expected :
    lowerBlockSummaries block = {expectedSummary} := by
  native_decide

private theorem bodyBranchModel_eq_expected :
    bodyBranchModel bodyPaths = {summaryAsBranch expectedPathSummary} := by
  native_decide

example : lowerBlockSummaries block = {expectedSummary} :=
  lowerBlockSummaries_eq_expected

example : bodyBranchModel bodyPaths = {summaryAsBranch expectedPathSummary} :=
  bodyBranchModel_eq_expected

private theorem h_contains : ∀ b ∈ bodyBranchModel bodyPaths, b.pc ∈ closure := by
  intro b hb
  have hb' : b = summaryAsBranch expectedPathSummary := by
    simpa [bodyBranchModel_eq_expected] using hb
  subst hb'
  simp [closure]

private theorem h_semClosed :
    SemClosed (vexSummaryISA ToyReg) (bodyBranchModel bodyPaths) closure := by
  intro b hb φ hφ s₁ s₂ _hEquiv
  have hb' : b = summaryAsBranch expectedPathSummary := by
    simpa [bodyBranchModel_eq_expected] using hb
  have hφ' : φ = expectedPathSummary.pc := by
    simpa [closure] using hφ
  subst hb'
  subst hφ'
  simp [vexSummaryISA, expectedPathSummary, expectedSummary, Summary.compose, Summary.id,
    satisfiesSymPC, substSymPC]

private theorem expectedPathSummary_apply (s : ConcreteState ToyReg) :
    Summary.apply expectedPathSummary s = execBlock block s := by
  have hLower : expectedSummary = lowerBlock block := by
    native_decide
  calc
    Summary.apply expectedPathSummary s
        = Summary.apply Summary.id (Summary.apply expectedSummary s) := by
            simp [expectedPathSummary, Summary.compose_apply]
    _ = Summary.apply expectedSummary s := by
          simp
    _ = execBlock block s := by
          simpa [hLower, Summary.apply] using (lowerBlock_sound block s)

private theorem h_sound :
    BranchModel.Sound (vexSummaryISA ToyReg)
      (↑(bodyBranchModel bodyPaths) : Set (Branch (SymSub ToyReg) (SymPC ToyReg)))
      behavior := by
  intro b hb s _hsat
  have hb' : b = summaryAsBranch expectedPathSummary := by
    simpa [bodyBranchModel_eq_expected] using hb
  subst hb'
  simpa [behavior, summaryAsBranch, vexSummaryISA] using expectedPathSummary_apply s

private theorem h_complete :
    BranchModel.Complete (vexSummaryISA ToyReg)
      (↑(bodyBranchModel bodyPaths) : Set (Branch (SymSub ToyReg) (SymPC ToyReg)))
      behavior := by
  intro s s' hs'
  refine ⟨summaryAsBranch expectedPathSummary, ?_, ?_, ?_⟩
  · simp [bodyBranchModel_eq_expected]
  · simp [expectedPathSummary, expectedSummary, Summary.compose, Summary.id,
      vexSummaryISA, satisfiesSymPC, substSymPC]
  ·
    subst hs'
    simpa [summaryAsBranch, vexSummaryISA] using expectedPathSummary_apply s

example :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith (vexSummaryISA ToyReg) closure))
      behavior
      (abstractBehaviorWith (vexSummaryISA ToyReg) (bodyBranchModel bodyPaths) closure) := by
  exact quotient_bisimulationSem (vexSummaryISA ToyReg)
    (bodyBranchModel bodyPaths) closure h_contains h_semClosed behavior h_sound h_complete

end Instances.Examples
